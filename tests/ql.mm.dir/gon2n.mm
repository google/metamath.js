include "wo.mm"
include "wa.mm"
include "wi2.mm"
include "lea.mm"
include "govar2.mm"
include "le2an.mm"
include "letr.mm"
include "ler2an.mm"
include "govar.mm"

theorem gon2n
  param wva: term a
  param wvb: term b
  param wvc: term c
  param wvd: term d
  param wve: term e
  assume govar.1: |- a =< b '
  assume govar.2: |- b =< c '
  assume gon2n.3: |- ( ( c ->2 a ) ^ d ) =< ( a ->2 c )
  assume gon2n.4: |- e =< d


  assert |- ( ( a v b ) ^ e ) =< ( b v c )

  proof
    wva
    wvb
    wo
    #
    wve
    wa
    #
    @0
    wva
    wvc
    wi2
    #
    wa
    wvb
    wvc
    wo
    @1
    @0
    @2
    @0
    wve
    lea
    @1
    wvc
    wva
    wi2
    #
    wvd
    wa
    @2
    @0
    @3
    wve
    wvd
    wva
    wvb
    wvc
    govar.1
    govar.2
    govar2
    gon2n.4
    le2an
    gon2n.3
    letr
    ler2an
    wva
    wvb
    wvc
    govar.1
    govar.2
    govar
    letr
end
