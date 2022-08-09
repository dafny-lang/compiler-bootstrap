module Utils {
  function method Max(x: int, y: int): int
  {
    if x > y then x else y
  }

  datatype Result<T> = | Success(value: T) | Failure
  {
    predicate method IsFailure() {
      Failure?
    }

    function method PropagateFailure(): Result<T>
      requires Failure?
    {
      Failure
    }

    function method Extract(): T
      requires Success?
    {
      value
    }
  }

  datatype Option<T> = Some(value: T) | None
}
