include "cv.mm"
include "wcel.mm"
include "ccsh.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "cfz.mm"
include "wrex.mm"
include "w3a.mm"
include "wa.mm"
include "wbr.mm"
include "df-3an.mm"
include "anidm.mm"
include "anbi1i.mm"
include "bitri.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "erclwwlkneq.mm"
include "mp2an.mm"
include "cclwwlkn.mm"
include "cvtx.mm"
include "cfv.mm"
include "cword.mm"
include "cn.mm"
include "eqid.mm"
include "clwwlknwrd.mm"
include "clwwlknnn.mm"
include "wi.mm"
include "cshw0.mm"
include "cn0.mm"
include "nnnn0.mm"
include "0elfz.mm"
include "syl.mm"
include "eqcom.mm"
include "biimpi.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anr.mm"
include "ex.mm"
include "sylc.mm"
include "eleq2s.mm"
include "pm4.71i.mm"
include "3bitr4ri.mm"

theorem erclwwlknref
  let vx: setvar x
  let vu: setvar u
  let vt: setvar t
  let c.sm: class .~
  let vn: setvar n
  let cG: class G
  let cN: class N
  let cW: class W
  assume erclwwlkn.w: |- W = ( N ClWWalksN G )
  assume erclwwlkn.r: |- .~ = { <. t , u >. | ( t e. W /\ u e. W /\ E. n e. ( 0 ... N ) t = ( u cyclShift n ) ) }

  disjoint W t
  disjoint W u
  disjoint t u
  disjoint N n
  disjoint N u
  disjoint N t
  disjoint N x
  disjoint n u
  disjoint n t
  disjoint n x
  disjoint u x
  disjoint t x
  assert |- ( x e. W <-> x .~ x )

  proof
    vx
    cv
    #
    cW
    wcel
    #
    @1
    @0
    @0
    vn
    cv
    #
    ccsh
    co
    #
    wceq
    #
    vn
    cc0
    cN
    cfz
    co
    #
    wrex
    #
    w3a
    #
    @1
    @6
    wa
    #
    @0
    @0
    c.sm
    wbr
    #
    @1
    @7
    @1
    @1
    wa
    #
    @6
    wa
    @8
    @1
    @1
    @6
    df-3an
    @10
    @1
    @6
    @1
    anidm
    anbi1i
    bitri
    @0
    cvv
    wcel
    #
    @11
    @9
    @7
    wb
    vx
    vex
    #
    @12
    vu
    vt
    c.sm
    @0
    @0
    vn
    cG
    cN
    cW
    cvv
    cvv
    erclwwlkn.w
    erclwwlkn.r
    erclwwlkneq
    mp2an
    @1
    @6
    @6
    @0
    cN
    cG
    cclwwlkn
    co
    #
    cW
    @0
    @13
    wcel
    @0
    cG
    cvtx
    cfv
    #
    cword
    wcel
    #
    cN
    cn
    wcel
    #
    @6
    cG
    cN
    @14
    @0
    @14
    eqid
    clwwlknwrd
    cG
    cN
    @0
    clwwlknnn
    @15
    @0
    cc0
    ccsh
    co
    #
    @0
    wceq
    #
    @16
    @6
    wi
    @14
    @0
    cshw0
    @18
    @16
    @6
    @16
    cc0
    @5
    wcel
    #
    @0
    @17
    wceq
    #
    @6
    @18
    @16
    cN
    cn0
    wcel
    @19
    cN
    nnnn0
    cN
    0elfz
    syl
    @18
    @20
    @17
    @0
    eqcom
    biimpi
    @4
    @20
    vn
    cc0
    @5
    @2
    cc0
    wceq
    @3
    @17
    @0
    @2
    cc0
    @0
    ccsh
    oveq2
    eqeq2d
    rspcev
    syl2anr
    ex
    syl
    sylc
    erclwwlkn.w
    eleq2s
    pm4.71i
    3bitr4ri
end
