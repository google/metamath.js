include "chs.mm"
include "wcel.mm"
include "cphl.mm"
include "cpj.mm"
include "cfv.mm"
include "cdm.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "eqid.mm"
include "ishil.mm"
include "wss.mm"
include "wb.mm"
include "pjcss.mm"
include "eqss.mm"
include "baib.mm"
include "syl.mm"
include "dfss3.mm"
include "syl6bb.mm"
include "clss.mm"
include "csslss.mm"
include "pjdm2.mm"
include "baibd.mm"
include "syldan.mm"
include "ralbidva.mm"
include "bitrd.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem ishil2
  let cC: class C
  let c.po: class .(+)
  let cH: class H
  let c.pe: class ._|_
  let cV: class V
  let vs: setvar s
  assume ishil2.v: |- V = ( Base ` H )
  assume ishil2.s: |- .(+) = ( LSSum ` H )
  assume ishil2.o: |- ._|_ = ( ocv ` H )
  assume ishil2.c: |- C = ( CSubSp ` H )

  disjoint C s
  disjoint H s
  assert |- ( H e. Hil <-> ( H e. PreHil /\ A. s e. C ( s .(+) ( ._|_ ` s ) ) = V ) )

  proof
    cH
    chs
    wcel
    cH
    cphl
    wcel
    #
    cH
    cpj
    cfv
    #
    cdm
    #
    cC
    wceq
    #
    wa
    @0
    vs
    cv
    #
    @4
    c.pe
    cfv
    c.po
    co
    cV
    wceq
    #
    vs
    cC
    wral
    #
    wa
    cC
    cH
    @1
    @1
    eqid
    #
    ishil2.c
    ishil
    @0
    @3
    @6
    @0
    @3
    @4
    @2
    wcel
    #
    vs
    cC
    wral
    #
    @6
    @0
    @3
    cC
    @2
    wss
    #
    @9
    @0
    @2
    cC
    wss
    #
    @3
    @10
    wb
    cC
    @1
    cH
    @7
    ishil2.c
    pjcss
    @3
    @11
    @10
    @2
    cC
    eqss
    baib
    syl
    vs
    cC
    @2
    dfss3
    syl6bb
    @0
    @8
    @5
    vs
    cC
    @0
    @4
    cC
    wcel
    @4
    cH
    clss
    cfv
    #
    wcel
    #
    @8
    @5
    wb
    cC
    @4
    @12
    cH
    ishil2.c
    @12
    eqid
    #
    csslss
    @0
    @8
    @13
    @5
    c.po
    @4
    @1
    @12
    c.pe
    cV
    cH
    ishil2.v
    @14
    ishil2.o
    ishil2.s
    @7
    pjdm2
    baibd
    syldan
    ralbidva
    bitrd
    pm5.32i
    bitri
end
