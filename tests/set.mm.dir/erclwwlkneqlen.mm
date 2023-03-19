include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "cv.mm"
include "ccsh.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "cfz.mm"
include "wrex.mm"
include "w3a.mm"
include "chash.mm"
include "cfv.mm"
include "erclwwlkneq.mm"
include "fveq2.mm"
include "cvtx.mm"
include "cword.mm"
include "cz.mm"
include "cclwwlkn.mm"
include "eqid.mm"
include "clwwlknwrd.mm"
include "eleq2s.mm"
include "adantl.mm"
include "elfzelz.mm"
include "cshwlen.mm"
include "syl2an.mm"
include "sylan9eqr.mm"
include "ex.mm"
include "rexlimdva.mm"
include "3impia.mm"
include "syl6bi.mm"

theorem erclwwlkneqlen
  let vu: setvar u
  let vt: setvar t
  let c.sm: class .~
  let cT: class T
  let cU: class U
  let vn: setvar n
  let cG: class G
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  assume erclwwlkn.w: |- W = ( N ClWWalksN G )
  assume erclwwlkn.r: |- .~ = { <. t , u >. | ( t e. W /\ u e. W /\ E. n e. ( 0 ... N ) t = ( u cyclShift n ) ) }

  disjoint N t
  disjoint N u
  disjoint t u
  disjoint T n
  disjoint T t
  disjoint T u
  disjoint n t
  disjoint n u
  disjoint U n
  disjoint U t
  disjoint U u
  disjoint W n
  disjoint X n
  disjoint Y n
  disjoint W t
  disjoint W u
  disjoint t u
  assert |- ( ( T e. X /\ U e. Y ) -> ( T .~ U -> ( # ` T ) = ( # ` U ) ) )

  proof
    cT
    cX
    wcel
    cU
    cY
    wcel
    wa
    cT
    cU
    c.sm
    wbr
    cT
    cW
    wcel
    #
    cU
    cW
    wcel
    #
    cT
    cU
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
    cT
    chash
    cfv
    #
    cU
    chash
    cfv
    #
    wceq
    #
    vu
    vt
    c.sm
    cT
    cU
    vn
    cG
    cN
    cW
    cX
    cY
    erclwwlkn.w
    erclwwlkn.r
    erclwwlkneq
    @0
    @1
    @6
    @9
    @0
    @1
    wa
    #
    @4
    @9
    vn
    @5
    @10
    @2
    @5
    wcel
    #
    wa
    #
    @4
    @9
    @4
    @12
    @7
    @3
    chash
    cfv
    #
    @8
    cT
    @3
    chash
    fveq2
    @10
    cU
    cG
    cvtx
    cfv
    #
    cword
    wcel
    #
    @2
    cz
    wcel
    @13
    @8
    wceq
    @11
    @1
    @15
    @0
    @15
    cU
    cN
    cG
    cclwwlkn
    co
    cW
    cG
    cN
    @14
    cU
    @14
    eqid
    clwwlknwrd
    erclwwlkn.w
    eleq2s
    adantl
    @2
    cc0
    cN
    elfzelz
    @2
    @14
    cU
    cshwlen
    syl2an
    sylan9eqr
    ex
    rexlimdva
    3impia
    syl6bi
end
