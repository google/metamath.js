include "wceq.mm"
include "cmpt.mm"
include "cgsu.mm"
include "co.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "cun.mm"
include "cmulr.mm"
include "cfv.mm"
include "difsnid.mm"
include "eqcomd.mm"
include "ad2antrl.mm"
include "mpteq1d.mm"
include "oveq2d.mm"
include "cbs.mm"
include "eqid.mm"
include "mgpbas.mm"
include "mgpplusg.mm"
include "ccmn.mm"
include "ccrg.mm"
include "crngmgp.mm"
include "syl.mm"
include "adantr.mm"
include "cfn.mm"
include "diffi.mm"
include "simpl.mm"
include "eldifi.mm"
include "syl2an.mm"
include "simprl.mm"
include "neldifsnd.mm"
include "crg.mm"
include "cmnd.mm"
include "crngring.mm"
include "ringmnd.mm"
include "mndidcl.mm"
include "3syl.mm"
include "wb.mm"
include "eleq1.mm"
include "ad2antll.mm"
include "mpbird.mm"
include "weq.mm"
include "adantlr.mm"
include "gsumunsnd.mm"
include "oveq2.mm"
include "sylan2.mm"
include "ralrimiva.mm"
include "gsummptcl.mm"
include "ringrz.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "3eqtrd.mm"
include "rexlimddv.mm"

theorem gsummgp0
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let vi: setvar i
  let vn: setvar n
  let cG: class G
  let cN: class N
  let c.0: class .0.
  assume gsummgp0.g: |- G = ( mulGrp ` R )
  assume gsummgp0.0: |- .0. = ( 0g ` R )
  assume gsummgp0.r: |- ( ph -> R e. CRing )
  assume gsummgp0.n: |- ( ph -> N e. Fin )
  assume gsummgp0.a: |- ( ( ph /\ n e. N ) -> A e. ( Base ` R ) )
  assume gsummgp0.e: |- ( ( ph /\ n = i ) -> A = B )
  assume gsummgp0.b: |- ( ph -> E. i e. N B = .0. )

  disjoint A i
  disjoint B n
  disjoint i n
  disjoint G i
  disjoint G n
  disjoint N i
  disjoint N n
  disjoint R n
  disjoint i ph
  disjoint n ph
  disjoint .0. i
  disjoint .0. n
  assert |- ( ph -> ( G gsum ( n e. N |-> A ) ) = .0. )

  proof
    wph
    cB
    c.0
    wceq
    #
    cG
    vn
    cN
    cA
    cmpt
    #
    cgsu
    co
    #
    c.0
    wceq
    vi
    cN
    gsummgp0.b
    wph
    vi
    cv
    #
    cN
    wcel
    #
    @0
    wa
    #
    wa
    #
    @2
    cG
    vn
    cN
    @3
    csn
    #
    cdif
    #
    @7
    cun
    #
    cA
    cmpt
    #
    cgsu
    co
    cG
    vn
    @8
    cA
    cmpt
    cgsu
    co
    #
    cB
    cR
    cmulr
    cfv
    #
    co
    #
    c.0
    @6
    @1
    @10
    cG
    cgsu
    @6
    vn
    cN
    @9
    cA
    @4
    cN
    @9
    wceq
    wph
    @0
    @4
    @9
    cN
    cN
    @3
    difsnid
    eqcomd
    ad2antrl
    mpteq1d
    oveq2d
    @6
    @8
    cR
    cbs
    cfv
    #
    @12
    vn
    cG
    @3
    cN
    cA
    cB
    @14
    cR
    cG
    gsummgp0.g
    @14
    eqid
    #
    mgpbas
    #
    cR
    @12
    cG
    gsummgp0.g
    @12
    eqid
    #
    mgpplusg
    wph
    cG
    ccmn
    wcel
    #
    @5
    wph
    cR
    ccrg
    wcel
    #
    @18
    gsummgp0.r
    cR
    cG
    gsummgp0.g
    crngmgp
    syl
    #
    adantr
    wph
    @8
    cfn
    wcel
    #
    @5
    wph
    cN
    cfn
    wcel
    @21
    gsummgp0.n
    cN
    @7
    diffi
    syl
    #
    adantr
    @6
    wph
    vn
    cv
    #
    cN
    wcel
    #
    cA
    @14
    wcel
    #
    @23
    @8
    wcel
    #
    wph
    @5
    simpl
    @23
    cN
    @7
    eldifi
    #
    gsummgp0.a
    syl2an
    wph
    @4
    @0
    simprl
    @6
    @3
    cN
    neldifsnd
    @6
    cB
    @14
    wcel
    #
    c.0
    @14
    wcel
    #
    wph
    @29
    @5
    wph
    cR
    crg
    wcel
    #
    cR
    cmnd
    wcel
    @29
    wph
    @19
    @30
    gsummgp0.r
    cR
    crngring
    syl
    #
    cR
    ringmnd
    @14
    cR
    c.0
    @15
    gsummgp0.0
    mndidcl
    3syl
    adantr
    @0
    @28
    @29
    wb
    wph
    @4
    cB
    c.0
    @14
    eleq1
    ad2antll
    mpbird
    wph
    vn
    vi
    weq
    cA
    cB
    wceq
    @5
    gsummgp0.e
    adantlr
    gsumunsnd
    @6
    @13
    @11
    c.0
    @12
    co
    #
    c.0
    @0
    @13
    @32
    wceq
    wph
    @4
    cB
    c.0
    @11
    @12
    oveq2
    ad2antll
    @6
    @30
    @11
    @14
    wcel
    #
    @32
    c.0
    wceq
    wph
    @30
    @5
    @31
    adantr
    wph
    @33
    @5
    wph
    @14
    vn
    cG
    @8
    cA
    @16
    @20
    @22
    wph
    @25
    vn
    @8
    @26
    wph
    @24
    @25
    @27
    gsummgp0.a
    sylan2
    ralrimiva
    gsummptcl
    adantr
    @14
    cR
    @12
    @11
    c.0
    @15
    @17
    gsummgp0.0
    ringrz
    syl2anc
    eqtrd
    3eqtrd
    rexlimddv
end
