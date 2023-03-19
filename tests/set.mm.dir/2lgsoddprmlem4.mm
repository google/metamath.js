include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "c8.mm"
include "cdiv.mm"
include "cmo.mm"
include "c7.mm"
include "cpr.mm"
include "wceq.mm"
include "wb.mm"
include "eqidd.mm"
include "2lgsoddprmlem2.mm"
include "mpd3an3.mm"
include "2lgsoddprmlem3.mm"
include "bitrd.mm"

theorem 2lgsoddprmlem4
  let cN: class N


  assert |- ( ( N e. ZZ /\ -. 2 || N ) -> ( 2 || ( ( ( N ^ 2 ) - 1 ) / 8 ) <-> ( N mod 8 ) e. { 1 , 7 } ) )

  proof
    cN
    cz
    wcel
    #
    c2
    cN
    cdvds
    wbr
    wn
    #
    wa
    #
    c2
    cN
    c2
    cexp
    co
    c1
    cmin
    co
    c8
    cdiv
    co
    cdvds
    wbr
    #
    c2
    cN
    c8
    cmo
    co
    #
    c2
    cexp
    co
    c1
    cmin
    co
    c8
    cdiv
    co
    cdvds
    wbr
    #
    @4
    c1
    c7
    cpr
    wcel
    #
    @0
    @1
    @4
    @4
    wceq
    #
    @3
    @5
    wb
    @2
    @4
    eqidd
    #
    @4
    cN
    2lgsoddprmlem2
    mpd3an3
    @0
    @1
    @7
    @5
    @6
    wb
    @8
    @4
    cN
    2lgsoddprmlem3
    mpd3an3
    bitrd
end
