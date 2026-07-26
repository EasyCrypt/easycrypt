module Make (B : Session.BACKEND) = struct
  module P = Pool.Make (B)

  type t = {
    correlation : Correlation.t;
    switch : Eio.Switch.t;
    deadline : float option;
    pool : P.t;
    publish : Publish.t;
  }
end
