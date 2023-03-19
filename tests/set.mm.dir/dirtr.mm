include "cdir.mm"
include "wcel.mm"
include "wbr.mm"
include "wa.mm"
include "cvv.mm"
include "wi.mm"
include "wrel.mm"
include "reldir.mm"
include "brrelex.mm"
include "ex.mm"
include "anim12d.mm"
include "syl.mm"
include "cv.mm"
include "wal.mm"
include "w3a.mm"
include "ccom.mm"
include "wss.mm"
include "cuni.mm"
include "cxp.mm"
include "ccnv.mm"
include "cid.mm"
include "cres.mm"
include "eqid.mm"
include "isdir.mm"
include "ibi.mm"
include "simprd.mm"
include "simpld.mm"
include "cotr.mm"
include "sylib.mm"
include "wceq.mm"
include "wb.mm"
include "breq12.mm"
include "3adant3.mm"
include "3adant1.mm"
include "anbi12d.mm"
include "3adant2.mm"
include "imbi12d.mm"
include "spc3gv.mm"
include "syl5.mm"
include "3expia.mm"
include "com4t.mm"
include "mpdd.mm"
include "imp31.mm"
include "an32s.mm"

theorem dirtr
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( ( R e. DirRel /\ C e. V ) /\ ( A R B /\ B R C ) ) -> A R C )

  proof
    cR
    cdir
    wcel
    #
    cA
    cB
    cR
    wbr
    #
    cB
    cC
    cR
    wbr
    #
    wa
    #
    cC
    cV
    wcel
    #
    cA
    cC
    cR
    wbr
    #
    @0
    @3
    @4
    @5
    @0
    @3
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    wa
    #
    @4
    @5
    wi
    @0
    cR
    wrel
    #
    @3
    @8
    wi
    cR
    reldir
    @9
    @1
    @6
    @2
    @7
    @9
    @1
    @6
    cA
    cB
    cR
    brrelex
    ex
    @9
    @2
    @7
    cB
    cC
    cR
    brrelex
    ex
    anim12d
    syl
    @8
    @4
    @0
    @3
    @5
    @6
    @7
    @4
    @0
    @3
    @5
    wi
    #
    wi
    @0
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    @12
    vz
    cv
    #
    cR
    wbr
    #
    wa
    #
    @11
    @14
    cR
    wbr
    #
    wi
    #
    vz
    wal
    vy
    wal
    vx
    wal
    #
    @6
    @7
    @4
    w3a
    @10
    @0
    cR
    cR
    ccom
    cR
    wss
    #
    @19
    @0
    @20
    cR
    cuni
    cuni
    #
    @21
    cxp
    cR
    ccnv
    cR
    ccom
    wss
    #
    @0
    @9
    cid
    @21
    cres
    cR
    wss
    wa
    #
    @20
    @22
    wa
    #
    @0
    @23
    @24
    wa
    @21
    cR
    cdir
    @21
    eqid
    isdir
    ibi
    simprd
    simpld
    vx
    vy
    vz
    cR
    cotr
    sylib
    @18
    @10
    vx
    vy
    vz
    cA
    cB
    cC
    cvv
    cvv
    cV
    @11
    cA
    wceq
    #
    @12
    cB
    wceq
    #
    @14
    cC
    wceq
    #
    w3a
    #
    @16
    @3
    @17
    @5
    @28
    @13
    @1
    @15
    @2
    @25
    @26
    @13
    @1
    wb
    @27
    @11
    cA
    @12
    cB
    cR
    breq12
    3adant3
    @26
    @27
    @15
    @2
    wb
    @25
    @12
    cB
    @14
    cC
    cR
    breq12
    3adant1
    anbi12d
    @25
    @27
    @17
    @5
    wb
    @26
    @11
    cA
    @14
    cC
    cR
    breq12
    3adant2
    imbi12d
    spc3gv
    syl5
    3expia
    com4t
    mpdd
    imp31
    an32s
end
