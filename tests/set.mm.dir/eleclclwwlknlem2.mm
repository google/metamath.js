include "cv.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "ccsh.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "simpl.mm"
include "anim1i.mm"
include "adantr.mm"
include "simpr.mm"
include "eleclclwwlknlem1.mm"
include "sylc.mm"
include "chash.mm"
include "cfv.mm"
include "cmin.mm"
include "wi.mm"
include "cvtx.mm"
include "cword.mm"
include "cclwwlkn.mm"
include "eqid.mm"
include "clwwlknbp.mm"
include "eleq2s.mm"
include "fznn0sub2.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "syl5ibr.mm"
include "adantl.mm"
include "syl.mm"
include "com12.mm"
include "imp.mm"
include "ancomd.mm"
include "jca.mm"
include "simpll.mm"
include "wb.mm"
include "oveq2.mm"
include "eleq2d.mm"
include "eqcoms.mm"
include "biimpa.mm"
include "ex.mm"
include "eqcomd.mm"
include "cz.mm"
include "elfzelz.mm"
include "2cshwid.mm"
include "sylan2.mm"
include "sylan9eqr.mm"
include "syl2anc.mm"
include "impbida.mm"

theorem eleclclwwlknlem2
  let vx: setvar x
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cG: class G
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let cK: class K
  let cZ: class Z
  assume erclwwlkn1.w: |- W = ( N ClWWalksN G )

  disjoint m n
  disjoint G m
  disjoint G n
  disjoint N m
  disjoint N n
  disjoint X m
  disjoint X n
  disjoint Y m
  disjoint Y n
  disjoint k m
  disjoint k n
  disjoint m x
  disjoint n x
  disjoint K m
  disjoint K n
  disjoint Z m
  disjoint Z n
  assert |- ( ( ( k e. ( 0 ... N ) /\ X = ( x cyclShift k ) ) /\ ( X e. W /\ x e. W ) ) -> ( E. m e. ( 0 ... N ) Y = ( x cyclShift m ) <-> E. n e. ( 0 ... N ) Y = ( X cyclShift n ) ) )

  proof
    vk
    cv
    #
    cc0
    cN
    cfz
    co
    #
    wcel
    #
    cX
    vx
    cv
    #
    @0
    ccsh
    co
    #
    wceq
    #
    wa
    #
    cX
    cW
    wcel
    #
    @3
    cW
    wcel
    #
    wa
    #
    wa
    #
    cY
    @3
    vm
    cv
    ccsh
    co
    wceq
    vm
    @1
    wrex
    #
    cY
    cX
    vn
    cv
    ccsh
    co
    wceq
    vn
    @1
    wrex
    #
    @10
    @11
    wa
    @2
    @9
    wa
    #
    @5
    @11
    wa
    @12
    @10
    @13
    @11
    @6
    @2
    @9
    @2
    @5
    simpl
    anim1i
    adantr
    @10
    @5
    @11
    @6
    @5
    @9
    @2
    @5
    simpr
    #
    adantr
    anim1i
    vm
    vn
    cG
    @0
    cN
    cW
    cX
    @3
    cY
    erclwwlkn1.w
    eleclclwwlknlem1
    sylc
    @10
    @12
    wa
    #
    @3
    chash
    cfv
    #
    @0
    cmin
    co
    #
    @1
    wcel
    #
    @8
    @7
    wa
    #
    wa
    @3
    cX
    @17
    ccsh
    co
    #
    wceq
    #
    @12
    wa
    @11
    @15
    @18
    @19
    @10
    @18
    @12
    @6
    @9
    @18
    @2
    @9
    @18
    wi
    @5
    @9
    @2
    @18
    @8
    @2
    @18
    wi
    #
    @7
    @8
    @3
    cG
    cvtx
    cfv
    #
    cword
    wcel
    #
    @16
    cN
    wceq
    #
    wa
    #
    @22
    @26
    @3
    cN
    cG
    cclwwlkn
    co
    cW
    cG
    cN
    @23
    @3
    @23
    eqid
    clwwlknbp
    erclwwlkn1.w
    eleq2s
    #
    @25
    @22
    @24
    @2
    @18
    @25
    cN
    @0
    cmin
    co
    #
    @1
    wcel
    @0
    cN
    fznn0sub2
    @25
    @17
    @28
    @1
    @16
    cN
    @0
    cmin
    oveq1
    eleq1d
    syl5ibr
    adantl
    syl
    adantl
    com12
    adantr
    imp
    adantr
    @10
    @19
    @12
    @10
    @7
    @8
    @6
    @9
    simpr
    ancomd
    adantr
    jca
    @10
    @21
    @12
    @10
    @20
    @3
    @10
    @24
    @0
    cc0
    @16
    cfz
    co
    #
    wcel
    #
    wa
    #
    @4
    cX
    wceq
    #
    @20
    @3
    wceq
    @6
    @9
    @31
    @2
    @9
    @31
    wi
    @5
    @9
    @2
    @31
    @8
    @2
    @31
    wi
    #
    @7
    @8
    @26
    @33
    @27
    @26
    @2
    @31
    @26
    @2
    wa
    @24
    @30
    @24
    @25
    @2
    simpll
    @26
    @2
    @30
    @25
    @2
    @30
    wb
    #
    @24
    @34
    cN
    @16
    cN
    @16
    wceq
    @1
    @29
    @0
    cN
    @16
    cc0
    cfz
    oveq2
    eleq2d
    eqcoms
    adantl
    biimpa
    jca
    ex
    syl
    adantl
    com12
    adantr
    imp
    @6
    @32
    @9
    @6
    cX
    @4
    @14
    eqcomd
    adantr
    @32
    @31
    @20
    @4
    @17
    ccsh
    co
    #
    @3
    @20
    @35
    wceq
    cX
    @4
    cX
    @4
    @17
    ccsh
    oveq1
    eqcoms
    @30
    @24
    @0
    cz
    wcel
    @35
    @3
    wceq
    @0
    cc0
    @16
    elfzelz
    @0
    @23
    @3
    2cshwid
    sylan2
    sylan9eqr
    syl2anc
    eqcomd
    anim1i
    vn
    vm
    cG
    @17
    cN
    cW
    @3
    cX
    cY
    erclwwlkn1.w
    eleclclwwlknlem1
    sylc
    impbida
end
