include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "ccsh.mm"
include "wceq.mm"
include "cv.mm"
include "wrex.mm"
include "cvtx.mm"
include "cfv.mm"
include "cword.mm"
include "chash.mm"
include "w3a.mm"
include "cclwwlkn.mm"
include "eqid.mm"
include "clwwlknbp.mm"
include "eleq2s.mm"
include "adantl.mm"
include "adantr.mm"
include "simpl.mm"
include "simprr.mm"
include "3jca.mm"
include "2cshwcshw.mm"
include "sylc.mm"
include "ex.mm"

theorem eleclclwwlknlem1
  let vm: setvar m
  let vn: setvar n
  let cG: class G
  let cK: class K
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume erclwwlkn1.w: |- W = ( N ClWWalksN G )

  disjoint m n
  disjoint G m
  disjoint G n
  disjoint K m
  disjoint K n
  disjoint N m
  disjoint N n
  disjoint X m
  disjoint X n
  disjoint Y m
  disjoint Y n
  disjoint Z m
  disjoint Z n
  assert |- ( ( K e. ( 0 ... N ) /\ ( X e. W /\ Y e. W ) ) -> ( ( X = ( Y cyclShift K ) /\ E. m e. ( 0 ... N ) Z = ( Y cyclShift m ) ) -> E. n e. ( 0 ... N ) Z = ( X cyclShift n ) ) )

  proof
    cK
    cc0
    cN
    cfz
    co
    #
    wcel
    #
    cX
    cW
    wcel
    #
    cY
    cW
    wcel
    #
    wa
    #
    wa
    #
    cX
    cY
    cK
    ccsh
    co
    wceq
    #
    cZ
    cY
    vm
    cv
    ccsh
    co
    wceq
    vm
    @0
    wrex
    #
    wa
    #
    cZ
    cX
    vn
    cv
    ccsh
    co
    wceq
    vn
    @0
    wrex
    #
    @5
    @8
    wa
    #
    cY
    cG
    cvtx
    cfv
    #
    cword
    wcel
    cY
    chash
    cfv
    cN
    wceq
    wa
    #
    @1
    @6
    @7
    w3a
    @9
    @5
    @12
    @8
    @4
    @12
    @1
    @3
    @12
    @2
    @12
    cY
    cN
    cG
    cclwwlkn
    co
    cW
    cG
    cN
    @11
    cY
    @11
    eqid
    clwwlknbp
    erclwwlkn1.w
    eleq2s
    adantl
    adantl
    adantr
    @10
    @1
    @6
    @7
    @5
    @1
    @8
    @1
    @4
    simpl
    adantr
    @8
    @6
    @5
    @6
    @7
    simpl
    adantl
    @5
    @6
    @7
    simprr
    3jca
    vm
    vn
    cK
    cN
    @11
    cX
    cY
    cZ
    2cshwcshw
    sylc
    ex
end
