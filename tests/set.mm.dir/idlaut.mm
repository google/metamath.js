include "wcel.mm"
include "cid.mm"
include "cres.mm"
include "wf1o.mm"
include "cv.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "wb.mm"
include "wral.mm"
include "f1oi.mm"
include "a1i.mm"
include "wa.mm"
include "fvresi.mm"
include "breqan12d.mm"
include "bicomd.mm"
include "rgen2a.mm"
include "eqid.mm"
include "islaut.mm"
include "mpbir2and.mm"

theorem idlaut
  let cA: class A
  let cB: class B
  let cI: class I
  let cK: class K
  let vx: setvar x
  let vy: setvar y
  assume idlaut.b: |- B = ( Base ` K )
  assume idlaut.i: |- I = ( LAut ` K )


  assert |- ( K e. A -> ( _I |` B ) e. I )

  proof
    cK
    cA
    wcel
    #
    cid
    cB
    cres
    #
    cI
    wcel
    cB
    cB
    @1
    wf1o
    #
    vx
    cv
    #
    vy
    cv
    #
    cK
    cple
    cfv
    #
    wbr
    #
    @3
    @1
    cfv
    #
    @4
    @1
    cfv
    #
    @5
    wbr
    #
    wb
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    @2
    @0
    cB
    f1oi
    a1i
    @11
    @0
    @10
    vx
    vy
    cB
    @3
    cB
    wcel
    #
    @4
    cB
    wcel
    #
    wa
    @9
    @6
    @12
    @13
    @7
    @3
    @8
    @4
    @5
    cB
    @3
    fvresi
    cB
    @4
    fvresi
    breqan12d
    bicomd
    rgen2a
    a1i
    vx
    vy
    cA
    cB
    @1
    cI
    cK
    @5
    idlaut.b
    @5
    eqid
    idlaut.i
    islaut
    mpbir2and
end
