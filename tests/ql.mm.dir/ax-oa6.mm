
axiom ax-oa6
  let wva: term a
  let wvb: term b
  let wvc: term c
  let wvd: term d
  let wve: term e
  let wvf: term f
  assume oal6.1: |- a =< b '
  assume oal6.2: |- c =< d '
  assume oal6.3: |- e =< f '
  assert |- ( ( ( a v b ) ^ ( c v d ) ) ^ ( e v f ) ) =< ( b v ( a ^ ( c v ( ( ( a v c ) ^ ( b v d ) ) ^ ( ( ( a v e ) ^ ( b v f ) ) v ( ( c v e ) ^ ( d v f ) ) ) ) ) ) )
end
