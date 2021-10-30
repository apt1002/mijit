/**
 * A first-in-first-out queue that remembers everything that was ever enqueued.
 */
#[derive(Debug)]
pub struct Fifo<T> {
    items: Vec<T>,
    done: usize,
}

impl<T> Fifo<T> {
    pub fn new() -> Self {
        Fifo {
            items: Vec::new(),
            done: 0,
        }
    }

    pub fn enqueue(&mut self, item: T) {
        self.items.push(item);
    }

    pub fn dequeue(&mut self) -> Option<&T> {
        if self.done >= self.items.len() {
            None
        } else {
            let item = &self.items[self.done];
            self.done += 1;
            Some(item)
        }
    }

    /** Returns all items that have ever been in the queue. */
    pub fn finish(self) -> Vec<T> {
        self.items
    }
}
