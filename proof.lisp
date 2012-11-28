;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; COMS W4701 Assignment #2: AUTOMATED THEOREM PROVER
;;; Evan Drewry - ewd2106 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; HEAP CODE FOR PRIORITY QUEUE
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defun heap-val (heap i key) (funcall key (elt heap i)))
(defun heap-parent (i) (floor (1- i) 2))
(defun heap-left (i) (+ 1 i i))
(defun heap-right (i) (+ 2 i i))
(defun heap-leafp (heap i) (> i (1- (floor (length heap) 2))))

(defun heapify (heap i key)
  "Assume that the children of i are heaps, but that heap[i]
   may be larger than its children. If it is, moves heap[i]
   down where it belongs."
  (unless (heap-leafp heap i)
    (let ((left-index (heap-left i))
          (right-index (heap-right i)))
      (let ((smaller-index
              (if (and (< right-index (length heap))
                       (< (heap-val heap right-index key)
                          (heap-val heap left-index key)))
                right-index
                left-index)))
        (when (> (heap-val heap i key)
                 (heap-val heap smaller-index key))
          (rotatef (elt heap i)
                   (elt heap smaller-index))
          (heapify heap smaller-index key))))
    ))

(defun heap-pop (heap key)
  "Pops the best (lowest valued) item off the heap."
  (let ((min (elt heap 0)))
    (setf (elt heap 0) (elt heap (1- (length heap))))
    (decf (fill-pointer heap))
    (heapify heap 0 key)
    min))

(defun heap-find-pos (heap i val key)
  "Bubbles up from i to find position for val, moving items
   down in the process"
  (cond ((or (zerop i)
             (< (heap-val heap (heap-parent i) key) val))
         i)
        (t (setf (elt heap i) (elt heap (heap-parent i)))
           (heap-find-pos heap (heap-parent i) val key))
        ))

(defun heap-insert (heap item key)
  "Puts an item into a heap"
  (vector-push-extend nil heap)
  (setf (elt heap (heap-find-pos heap (1- (length heap))
                                 (funcall key item) key))
        item)
  )

(defun make-heap (&optional (size 100))
  (make-array size :fill-pointer 0 :adjustable t))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; QUEUE CODE FOR SEARCH ALGORITHMS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defstruct q
  (enqueue #'enqueue-FIFO)
  (key #'identity)
  (last nil)
  (elements nil))

(defun q-emptyp (q)
  "Returns T if queue is empty."
  (= (length (q-elements q)) 0))

(defun q-front (q)
  "Returns the element at the front of the queue."
  (elt (q-elements q) 0))

(defun q-remove (q)
  "Removes and returns the element at the front of the queue."
  (if (listp (q-elements q))
    (pop (q-elements q))
    (heap-pop (q-elements q) (q-key q))))

(defun q-insert (q items)
  "Inserts the items into the queue, according to the
   queue's enqueuing function. Returns the altered queue."
  (funcall (q-enqueue q) q items)
  q)

(defun enqueue-LIFO (q items)
  "Adds a list of items to the front fo the queue."
  (setf (q-elements q) (nconc items (q-elements q)))
  items)

(defun enqueue-FIFO (q items)
  "Adds a list of items to the end of the queue."
  (if  (q-emptyp q)
    (setf (q-elements q) items)
    (setf (cdr (q-last q)) items))
  (setf (q-last q) (last items))
  items)

(defun enqueue-priority (q items)
  "Inserts the items by priority of key values."
  (when (null (q-elements q))
    (setf (q-elements q) (make-heap)))
  (mapc (lambda (item)
          (heap-insert (q-elements q) item (q-key q)))
        items)
  items)



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; GENERAL SEARCH CODE & ALGORITHMS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defvar *nodes-expanded* 0)

(defstruct node 
  (state nil)
  (parent nil)
  (action nil)
  (path-cost 0)
  (depth 0))

(defun action-sequence (node &optional (actions nil))
  (if (node-parent node)
    (action-sequence (node-parent node)
                     (cons (node-action node) actions))
    actions))

(defun expand (successor node)
  "Increments *nodes-expanded* and expands the node using the
   successor function."
  (incf *nodes-expanded*)
  (let ((triples (funcall successor (node-state node))))
    (mapcar (lambda (action-state-cost)
             (let ((action (car action-state-cost))
                    (state (cadr action-state-cost))
                    (cost (caddr action-state-cost)))
                (make-node :state state
                           :parent node
                           :action action
                           :path-cost (+ (node-path-cost node)
                                         cost)
                           :depth (1+ (node-depth node)))
                ))
            triples)
    ))

(defun tree-search (fringe successor goalp)
  "General tree search."
  (unless (q-emptyp fringe)
    (let ((node (q-remove fringe)))
      (if (funcall goalp (node-state node))
        (action-sequence node)
        (tree-search (q-insert fringe (expand successor node))
                     successor goalp))
      )))

(defun graph-search (fringe closed successor goalp samep)
  "General tree search."
  (unless (q-emptyp fringe)
    (let ((node (q-remove fringe)))
      (cond ((funcall goalp (node-state node))
             (action-sequence node))
            ((member (node-state node) closed
                     :test samep :key #'node-state)
             (graph-search fringe closed
                           successor goalp samep))
            (t (let ((successors (expand successor node)))
                 (graph-search (q-insert fringe successors)
                               (cons node closed)
                               successor goalp samep)))
            ))
    ))

(defun general-search (initial-state successor goalp
                       &key (samep #'eql)
                            (enqueue #'enqueue-LIFO)
                            (key #'identity))
  "General search."
  (setf *nodes-expanded* 0)    
  (let ((fringe (make-q :enqueue enqueue :key key)))
    (q-insert fringe (list (make-node :state initial-state)))
    (let ((result (graph-search fringe nil successor goalp samep)))
      (list result (length result) *nodes-expanded*))))

(defun a-star-search (initial-state successor goalp samep heuristic)
  "General A* search."
  (general-search initial-state successor goalp
                  :samep samep
                  :enqueue #'enqueue-priority
                  :key (lambda (node)
                         (+ (funcall heuristic node)
                            (node-path-cost node)))))





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PROOF CODE
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defstruct proof-state
  (kb nil)
  (resolvers nil)
  (theta nil))

(defun starts-with-p (char string)
  "Check if input string starts with input char"
  (equal (elt string 0) char))

(defun varp (x)                                                          
  "Check if the input x is supposed to be bound to a variable; i.e. if the
  symbol passed in begins with an quesion mark"
  (and (symbolp x) (starts-with-p #\? (symbol-name x))))

(defun unify (x y &optional theta)
  (cond ((eql theta 'fail) 'fail)
        ((eql x y) theta)
        ((varp x) (unify-var x y theta))
        ((varp y) (unify-var y x theta))
        ((and (consp x) (consp y))
         (unify (cdr x) (cdr y) (unify (car x) (car y) theta)))
        (t 'fail)))

(defun unify-var (var x theta)
  (let ((vb (assoc var theta))
        (xb (assoc x theta)))
    (cond (vb (unify (cdr vb) x theta))
          (xb (unify var (cdr xb) theta))
          ((occurs-p var x theta) 'fail)
          (t (cons (cons var x) theta)))))

(defun occurs-p (var x theta)
  (cond ((eql var x) t)
        ((and (varp x) (assoc x theta))
         (occurs-p var (cdr (assoc x theta)) theta))
        ((consp x) (or (occurs-p var (car x) theta)
                       (occurs-p var (cdr x) theta)))
        (t nil)))

(defun single-term-clause-p (clause)
  (reduce #'(lambda (x y)
              (and x y))
          (mapcar #'(lambda (term) 
                      (or (atom term)
                          (and (listp term)
                               (equal '_not (car term))
                               (single-term-clause-p (cdr term)))))
                  clause)))

(defun resolve-clause (clause resolver)
  t)

(defun proof-goalp (proof-state)
  (null (proof-state-resolvers proof-state)))

(defun proof-successor (proof-state)
  (remove 'fail (mapcar #'(lambda (kb-member)
                            (resolve-clause kb-member
                                            (proof-state-resolvers proof-state)))
                        (proof-state-kb proof-state))))

(defun resolve (initial-state)
  (general-search initial-state #'proof-successor #'proof-goalp))

(defun list-of-cnf (cnf)
  (mapcar #'cdr (cdr cnf)))

(defun atp (knowledge-base negated-query)
  "Automated theorem prover (ATP) for First-Order Logic (FOL). Takes
  two arguments: KB = a list of sentences considered to be axioms
  represented in Skolem Normal Form (SNF), and nq = a sentence also
  in SNF representing the negated version of the sentence to be proven."
  (let ((kb (list-of-cnf knowledge-base))
        (resolvers (list-of-cnf negated-query)))
    (resolve (make-proof-state :kb kb
                               :resolvers resolvers))))
