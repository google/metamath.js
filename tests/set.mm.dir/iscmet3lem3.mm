include "cz.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cv.mm"
include "cexp.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "cmpt.mm"
include "simpl.mm"
include "simpr.mm"
include "wceq.mm"
include "eluzelz.mm"
include "eleq2s.mm"
include "adantl.mm"
include "oveq2.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl.mm"
include "cc0.mm"
include "cres.mm"
include "cli.mm"
include "cn0.mm"
include "nn0uz.mm"
include "reseq2i.mm"
include "wss.mm"
include "nn0ssz.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "eqtr3i.mm"
include "cc.mm"
include "halfcn.mm"
include "a1i.mm"
include "cr.mm"
include "cle.mm"
include "halfre.mm"
include "1rp.mm"
include "rphalfcl.mm"
include "rpge0.mm"
include "absid.mm"
include "mp2an.mm"
include "halflt1.mm"
include "eqbrtri.mm"
include "expcnv.mm"
include "syl5eqbr.mm"
include "cvv.mm"
include "wb.mm"
include "0z.mm"
include "zex.mm"
include "mptex.mm"
include "climres.mm"
include "sylancr.mm"
include "mpbid.mm"
include "climi0.mm"
include "uztrn2.mm"
include "rpexpcl.mm"
include "rpre.mm"
include "absidd.mm"
include "breq1d.mm"
include "sylan2.mm"
include "anassrs.mm"
include "ralbidva.mm"
include "rexbidva.mm"

theorem iscmet3lem3
  let cR: class R
  let vj: setvar j
  let vk: setvar k
  let cM: class M
  let cZ: class Z
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let vn: setvar n
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let cG: class G
  let cF: class F
  let cX: class X
  let cJ: class J
  let cS: class S
  let wph: wff ph
  assume iscmet3.1: |- Z = ( ZZ>= ` M )

  disjoint j k
  disjoint R j
  disjoint R k
  disjoint Z j
  disjoint Z k
  disjoint M j
  disjoint M k
  disjoint f g
  disjoint f i
  disjoint f j
  disjoint f k
  disjoint f n
  disjoint f r
  disjoint f s
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint f x
  disjoint f y
  disjoint D f
  disjoint g i
  disjoint g j
  disjoint g k
  disjoint g n
  disjoint g r
  disjoint g s
  disjoint g t
  disjoint g u
  disjoint g v
  disjoint g x
  disjoint g y
  disjoint D g
  disjoint i j
  disjoint i k
  disjoint i n
  disjoint i r
  disjoint i s
  disjoint i t
  disjoint i u
  disjoint i v
  disjoint i x
  disjoint i y
  disjoint D i
  disjoint j n
  disjoint j r
  disjoint j s
  disjoint j t
  disjoint j u
  disjoint j v
  disjoint j x
  disjoint j y
  disjoint D j
  disjoint k n
  disjoint k r
  disjoint k s
  disjoint k t
  disjoint k u
  disjoint k v
  disjoint k x
  disjoint k y
  disjoint D k
  disjoint n r
  disjoint n s
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n x
  disjoint n y
  disjoint D n
  disjoint r s
  disjoint r t
  disjoint r u
  disjoint r v
  disjoint r x
  disjoint r y
  disjoint D r
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s x
  disjoint s y
  disjoint D s
  disjoint t u
  disjoint t v
  disjoint t x
  disjoint t y
  disjoint D t
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint D u
  disjoint v x
  disjoint v y
  disjoint D v
  disjoint x y
  disjoint D x
  disjoint D y
  disjoint G j
  disjoint G k
  disjoint G r
  disjoint G x
  disjoint G y
  disjoint F j
  disjoint F k
  disjoint F n
  disjoint F r
  disjoint F u
  disjoint F v
  disjoint F x
  disjoint F y
  disjoint X f
  disjoint X g
  disjoint X i
  disjoint X j
  disjoint X k
  disjoint X n
  disjoint X r
  disjoint X s
  disjoint X x
  disjoint X y
  disjoint J f
  disjoint J g
  disjoint J i
  disjoint J j
  disjoint J k
  disjoint J n
  disjoint J r
  disjoint J s
  disjoint J x
  disjoint J y
  disjoint S k
  disjoint S n
  disjoint S u
  disjoint S v
  disjoint S y
  disjoint Z f
  disjoint Z g
  disjoint Z i
  disjoint Z n
  disjoint Z r
  disjoint Z s
  disjoint Z y
  disjoint M f
  disjoint M i
  disjoint M n
  disjoint M x
  disjoint f ph
  disjoint g ph
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint n ph
  disjoint ph r
  disjoint ph s
  disjoint ph x
  disjoint ph y
  assert |- ( ( M e. ZZ /\ R e. RR+ ) -> E. j e. Z A. k e. ( ZZ>= ` j ) ( ( 1 / 2 ) ^ k ) < R )

  proof
    cM
    cz
    wcel
    #
    cR
    crp
    wcel
    #
    wa
    #
    c1
    c2
    cdiv
    co
    #
    vk
    cv
    #
    cexp
    co
    #
    cabs
    cfv
    #
    cR
    clt
    wbr
    #
    vk
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vj
    cZ
    wrex
    @5
    cR
    clt
    wbr
    #
    vk
    @9
    wral
    #
    vj
    cZ
    wrex
    @2
    @5
    cR
    vj
    vk
    vn
    cz
    @3
    vn
    cv
    #
    cexp
    co
    #
    cmpt
    #
    cM
    cZ
    iscmet3.1
    @0
    @1
    simpl
    @0
    @1
    simpr
    @2
    @4
    cZ
    wcel
    #
    wa
    #
    @4
    cz
    wcel
    #
    @4
    @15
    cfv
    @5
    wceq
    @16
    @18
    @2
    @18
    @4
    cM
    cuz
    cfv
    cZ
    cM
    @4
    eluzelz
    iscmet3.1
    eleq2s
    adantl
    #
    vn
    @4
    @14
    @5
    cz
    @15
    @13
    @4
    @3
    cexp
    oveq2
    @15
    eqid
    @3
    @4
    cexp
    ovex
    fvmpt
    syl
    @2
    @15
    cc0
    cuz
    cfv
    #
    cres
    #
    cc0
    cli
    wbr
    #
    @15
    cc0
    cli
    wbr
    #
    @2
    @21
    vn
    cn0
    @14
    cmpt
    #
    cc0
    cli
    @15
    cn0
    cres
    #
    @21
    @24
    cn0
    @20
    @15
    nn0uz
    reseq2i
    cn0
    cz
    wss
    @25
    @24
    wceq
    nn0ssz
    vn
    cz
    cn0
    @14
    resmpt
    ax-mp
    eqtr3i
    @2
    @3
    vn
    @3
    cc
    wcel
    @2
    halfcn
    a1i
    @3
    cabs
    cfv
    #
    c1
    clt
    wbr
    @2
    @26
    @3
    c1
    clt
    @3
    cr
    wcel
    cc0
    @3
    cle
    wbr
    #
    @26
    @3
    wceq
    halfre
    @3
    crp
    wcel
    #
    @27
    c1
    crp
    wcel
    @28
    1rp
    c1
    rphalfcl
    ax-mp
    #
    @3
    rpge0
    ax-mp
    @3
    absid
    mp2an
    halflt1
    eqbrtri
    a1i
    expcnv
    syl5eqbr
    @2
    cc0
    cz
    wcel
    @15
    cvv
    wcel
    #
    @22
    @23
    wb
    0z
    @30
    @2
    vn
    cz
    @14
    zex
    mptex
    a1i
    cc0
    @15
    cc0
    cvv
    climres
    sylancr
    mpbid
    climi0
    @2
    @10
    @12
    vj
    cZ
    @2
    @8
    cZ
    wcel
    #
    wa
    @7
    @11
    vk
    @9
    @2
    @31
    @4
    @9
    wcel
    #
    @7
    @11
    wb
    #
    @31
    @32
    wa
    @2
    @16
    @33
    cM
    @4
    @8
    cZ
    iscmet3.1
    uztrn2
    @17
    @6
    @5
    cR
    clt
    @17
    @5
    crp
    wcel
    #
    @6
    @5
    wceq
    @17
    @28
    @18
    @34
    @29
    @19
    @3
    @4
    rpexpcl
    sylancr
    @34
    @5
    @5
    rpre
    @5
    rpge0
    absidd
    syl
    breq1d
    sylan2
    anassrs
    ralbidva
    rexbidva
    mpbid
end
