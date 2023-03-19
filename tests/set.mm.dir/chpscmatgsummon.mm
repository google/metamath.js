include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "w3a.mm"
include "cfv.mm"
include "cc0.mm"
include "chash.mm"
include "cfz.mm"
include "cbc.mm"
include "cmin.mm"
include "cmpt.mm"
include "cgsu.mm"
include "chpscmatgsumbin.mm"
include "csca.mm"
include "cmg.mm"
include "clmod.mm"
include "cbs.mm"
include "cn0.mm"
include "crg.mm"
include "crngring.mm"
include "adantl.mm"
include "ply1lmod.mm"
include "syl.mm"
include "ad2antrr.mm"
include "cmnd.mm"
include "ringmgp.mm"
include "fznn0sub.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "adantr.mm"
include "simp2.mm"
include "weq.mm"
include "c0g.mm"
include "cif.mm"
include "wrex.mm"
include "crab.mm"
include "elrabi.mm"
include "eleq2s.mm"
include "3ad2ant1.mm"
include "3jca.mm"
include "eqid.mm"
include "matecl.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "mgpbas.mm"
include "mulgnn0cl.mm"
include "syl3anc.mm"
include "ply1sca.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "eleqtrrd.mm"
include "cz.mm"
include "hashcl.mm"
include "elfzelz.mm"
include "bccl.mm"
include "syl2an.mm"
include "ply1ring.mm"
include "3syl.mm"
include "elfznn0.mm"
include "vr1cl.mm"
include "lmodvsmmulgdi.mm"
include "syl13anc.mm"
include "syl5req.mm"
include "oveqd.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"

theorem chpscmatgsummon
  let cA: class A
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let vi: setvar i
  let vj: setvar j
  let vm: setvar m
  let vn: setvar n
  let cE: class E
  let c.ex: class .^
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cJ: class J
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let cZ: class Z
  let vc: setvar c
  let vl: setvar l
  let vk: setvar k
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  assume chp0mat.c: |- C = ( N CharPlyMat R )
  assume chp0mat.p: |- P = ( Poly1 ` R )
  assume chp0mat.a: |- A = ( N Mat R )
  assume chp0mat.x: |- X = ( var1 ` R )
  assume chp0mat.g: |- G = ( mulGrp ` P )
  assume chp0mat.m: |- .^ = ( .g ` G )
  assume chpscmat.d: |- D = { m e. ( Base ` A ) | E. c e. ( Base ` R ) A. i e. N A. j e. N ( i m j ) = if ( i = j , c , ( 0g ` R ) ) }
  assume chpscmat.s: |- S = ( algSc ` P )
  assume chpscmat.m: |- .- = ( -g ` P )
  assume chpscmatgsum.f: |- F = ( .g ` P )
  assume chpscmatgsum.h: |- H = ( mulGrp ` R )
  assume chpscmatgsum.e: |- E = ( .g ` H )
  assume chpscmatgsum.i: |- I = ( invg ` R )
  assume chpscmatgsum.s: |- .x. = ( .s ` P )
  assume chpscmatgsum.z: |- Z = ( .g ` R )

  disjoint A c
  disjoint A m
  disjoint c m
  disjoint D n
  disjoint E n
  disjoint I n
  disjoint M c
  disjoint M i
  disjoint M j
  disjoint M m
  disjoint M n
  disjoint c i
  disjoint c j
  disjoint c n
  disjoint i j
  disjoint i m
  disjoint i n
  disjoint j m
  disjoint j n
  disjoint m n
  disjoint N c
  disjoint N m
  disjoint N n
  disjoint P n
  disjoint R c
  disjoint R m
  disjoint R n
  disjoint S n
  disjoint D l
  disjoint F l
  disjoint I l
  disjoint J l
  disjoint J n
  disjoint l n
  disjoint M l
  disjoint N l
  disjoint P l
  disjoint R l
  disjoint S l
  disjoint X l
  disjoint .^ l
  disjoint i j
  disjoint A i
  disjoint A j
  disjoint N i
  disjoint N j
  disjoint P i
  disjoint P j
  disjoint R i
  disjoint R j
  disjoint X i
  disjoint X j
  disjoint D k
  disjoint k n
  disjoint E k
  disjoint I k
  disjoint M k
  disjoint c k
  disjoint i k
  disjoint j k
  disjoint k m
  disjoint S k
  disjoint .- k
  disjoint .0. i
  disjoint .0. j
  disjoint .0. k
  disjoint i k
  disjoint j k
  disjoint A k
  disjoint G k
  disjoint N k
  disjoint N x
  disjoint N y
  disjoint i x
  disjoint i y
  disjoint j x
  disjoint j y
  disjoint k x
  disjoint k y
  disjoint x y
  disjoint P k
  disjoint R k
  disjoint R x
  disjoint R y
  disjoint X k
  assert |- ( ( ( N e. Fin /\ R e. CRing ) /\ ( M e. D /\ J e. N /\ A. n e. N ( n M n ) = ( J M J ) ) ) -> ( C ` M ) = ( P gsum ( l e. ( 0 ... ( # ` N ) ) |-> ( ( ( ( # ` N ) _C l ) Z ( ( ( # ` N ) - l ) E ( I ` ( J M J ) ) ) ) .x. ( l .^ X ) ) ) ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    ccrg
    wcel
    #
    wa
    #
    cM
    cD
    wcel
    #
    cJ
    cN
    wcel
    #
    vn
    cv
    #
    @5
    cM
    co
    cJ
    cJ
    cM
    co
    #
    wceq
    vn
    cN
    wral
    #
    w3a
    #
    wa
    #
    cM
    cC
    cfv
    cP
    vl
    cc0
    cN
    chash
    cfv
    #
    cfz
    co
    #
    @10
    vl
    cv
    #
    cbc
    co
    #
    @10
    @12
    cmin
    co
    #
    @6
    cI
    cfv
    #
    cE
    co
    #
    @12
    cX
    c.ex
    co
    #
    c.x
    co
    cF
    co
    #
    cmpt
    #
    cgsu
    co
    cP
    vl
    @11
    @13
    @16
    cZ
    co
    #
    @17
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    cA
    cC
    cD
    cP
    cR
    cS
    c.x
    vi
    vj
    vm
    vn
    cE
    c.ex
    cF
    cG
    cH
    cI
    cJ
    cM
    c.mi
    cN
    cX
    vc
    vl
    chp0mat.c
    chp0mat.p
    chp0mat.a
    chp0mat.x
    chp0mat.g
    chp0mat.m
    chpscmat.d
    chpscmat.s
    chpscmat.m
    chpscmatgsum.f
    chpscmatgsum.h
    chpscmatgsum.e
    chpscmatgsum.i
    chpscmatgsum.s
    chpscmatgsumbin
    @9
    @19
    @22
    cP
    cgsu
    @9
    vl
    @11
    @18
    @21
    @9
    @12
    @11
    wcel
    #
    wa
    #
    @18
    @13
    @16
    cP
    csca
    cfv
    #
    cmg
    cfv
    #
    co
    #
    @17
    c.x
    co
    #
    @21
    @24
    cP
    clmod
    wcel
    #
    @16
    @25
    cbs
    cfv
    #
    wcel
    @13
    cn0
    wcel
    #
    @17
    cP
    cbs
    cfv
    #
    wcel
    #
    @18
    @28
    wceq
    @2
    @29
    @8
    @23
    @2
    cR
    crg
    wcel
    #
    @29
    @1
    @34
    @0
    cR
    crngring
    #
    adantl
    #
    cP
    cR
    chp0mat.p
    ply1lmod
    syl
    ad2antrr
    @24
    @16
    cR
    cbs
    cfv
    #
    @30
    @24
    cH
    cmnd
    wcel
    #
    @14
    cn0
    wcel
    #
    @15
    @37
    wcel
    #
    @16
    @37
    wcel
    @2
    @38
    @8
    @23
    @2
    @34
    @38
    @36
    cR
    cH
    chpscmatgsum.h
    ringmgp
    syl
    ad2antrr
    @23
    @39
    @9
    @12
    cc0
    @10
    fznn0sub
    adantl
    @9
    @40
    @23
    @9
    cR
    cgrp
    wcel
    #
    @6
    @37
    wcel
    #
    @40
    @2
    @41
    @8
    @1
    @41
    @0
    @1
    @34
    @41
    @35
    cR
    ringgrp
    syl
    adantl
    adantr
    @9
    @4
    @4
    cM
    cA
    cbs
    cfv
    #
    wcel
    #
    w3a
    #
    @42
    @8
    @45
    @2
    @8
    @4
    @4
    @44
    @3
    @4
    @7
    simp2
    #
    @46
    @3
    @4
    @44
    @7
    @44
    cM
    vi
    cv
    vj
    cv
    vm
    cv
    co
    vi
    vj
    weq
    vc
    cv
    cR
    c0g
    cfv
    cif
    wceq
    vj
    cN
    wral
    vi
    cN
    wral
    vc
    @37
    wrex
    #
    vm
    @43
    crab
    cD
    @47
    vm
    cM
    @43
    elrabi
    chpscmat.d
    eleq2s
    3ad2ant1
    3jca
    adantl
    cA
    cR
    cJ
    cJ
    @37
    cM
    cN
    chp0mat.a
    @37
    eqid
    #
    matecl
    syl
    @37
    cR
    cI
    @6
    @48
    chpscmatgsum.i
    grpinvcl
    syl2anc
    adantr
    @37
    cE
    cH
    @14
    @15
    @37
    cR
    cH
    chpscmatgsum.h
    @48
    mgpbas
    chpscmatgsum.e
    mulgnn0cl
    syl3anc
    @2
    @30
    @37
    wceq
    @8
    @23
    @2
    @25
    cR
    cbs
    @2
    cR
    @25
    @1
    cR
    @25
    wceq
    @0
    cP
    cR
    ccrg
    chp0mat.p
    ply1sca
    adantl
    #
    eqcomd
    fveq2d
    ad2antrr
    eleqtrrd
    @9
    @10
    cn0
    wcel
    #
    @12
    cz
    wcel
    @31
    @23
    @0
    @50
    @1
    @8
    cN
    hashcl
    ad2antrr
    @12
    cc0
    @10
    elfzelz
    @12
    @10
    bccl
    syl2an
    @24
    cG
    cmnd
    wcel
    #
    @12
    cn0
    wcel
    #
    cX
    @32
    wcel
    #
    @33
    @2
    @51
    @8
    @23
    @1
    @51
    @0
    @1
    @34
    cP
    crg
    wcel
    @51
    @35
    cP
    cR
    chp0mat.p
    ply1ring
    cP
    cG
    chp0mat.g
    ringmgp
    3syl
    adantl
    ad2antrr
    @23
    @52
    @9
    @12
    @10
    elfznn0
    adantl
    @2
    @53
    @8
    @23
    @2
    @34
    @53
    @36
    @32
    cP
    cR
    cX
    chp0mat.x
    chp0mat.p
    @32
    eqid
    #
    vr1cl
    syl
    ad2antrr
    @32
    c.ex
    cG
    @12
    cX
    @32
    cP
    cG
    chp0mat.g
    @54
    mgpbas
    chp0mat.m
    mulgnn0cl
    syl3anc
    @16
    c.x
    @26
    cF
    @25
    @30
    @13
    @32
    cP
    @17
    @54
    @25
    eqid
    chpscmatgsum.s
    @30
    eqid
    chpscmatgsum.f
    @26
    eqid
    lmodvsmmulgdi
    syl13anc
    @24
    @27
    @20
    @17
    c.x
    @24
    @26
    cZ
    @13
    @16
    @2
    @26
    cZ
    wceq
    @8
    @23
    @2
    cZ
    cR
    cmg
    cfv
    @26
    chpscmatgsum.z
    @2
    cR
    @25
    cmg
    @49
    fveq2d
    syl5req
    ad2antrr
    oveqd
    oveq1d
    eqtrd
    mpteq2dva
    oveq2d
    eqtrd
end
