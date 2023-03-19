include "cfv.mm"
include "crgspn.mm"
include "cv.mm"
include "wss.mm"
include "csubrg.mm"
include "crab.mm"
include "cint.mm"
include "fveq1d.mm"
include "cbs.mm"
include "cpw.mm"
include "cmpt.mm"
include "crg.mm"
include "wcel.mm"
include "cvv.mm"
include "wceq.mm"
include "elex.mm"
include "fveq2.mm"
include "pweqd.mm"
include "rabeq.mm"
include "syl.mm"
include "inteqd.mm"
include "mpteq12dv.mm"
include "df-rgspn.mm"
include "fvex.mm"
include "pwex.mm"
include "mptex.mm"
include "fvmpt.mm"
include "3syl.mm"
include "sseqtrd.mm"
include "elpw2.mm"
include "sylibr.mm"
include "wrex.mm"
include "eqid.mm"
include "subrgid.mm"
include "eqeltrd.mm"
include "sseq2.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "intexrab.mm"
include "sylib.mm"
include "sseq1.mm"
include "rabbidv.mm"
include "fvmptg.mm"
include "eqtrd.mm"
include "3eqtrd.mm"

theorem rgspnval
  let wph: wff ph
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cR: class R
  let cU: class U
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let cS: class S
  assume rgspnval.r: |- ( ph -> R e. Ring )
  assume rgspnval.b: |- ( ph -> B = ( Base ` R ) )
  assume rgspnval.ss: |- ( ph -> A C_ B )
  assume rgspnval.n: |- ( ph -> N = ( RingSpan ` R ) )
  assume rgspnval.sp: |- ( ph -> U = ( N ` A ) )

  disjoint ph t
  disjoint R t
  disjoint B t
  disjoint A t
  disjoint a ph
  disjoint b ph
  disjoint a b
  disjoint a t
  disjoint b t
  disjoint R a
  disjoint R b
  disjoint B a
  disjoint B b
  disjoint A a
  disjoint A b
  disjoint S t
  assert |- ( ph -> U = |^| { t e. ( SubRing ` R ) | A C_ t } )

  proof
    wph
    cU
    cA
    cN
    cfv
    cA
    cR
    crgspn
    cfv
    #
    cfv
    #
    cA
    vt
    cv
    #
    wss
    #
    vt
    cR
    csubrg
    cfv
    #
    crab
    #
    cint
    #
    rgspnval.sp
    wph
    cA
    cN
    @0
    rgspnval.n
    fveq1d
    wph
    @1
    cA
    vb
    cR
    cbs
    cfv
    #
    cpw
    #
    vb
    cv
    #
    @2
    wss
    #
    vt
    @4
    crab
    #
    cint
    #
    cmpt
    #
    cfv
    #
    @6
    wph
    cA
    @0
    @13
    wph
    cR
    crg
    wcel
    #
    cR
    cvv
    wcel
    @0
    @13
    wceq
    rgspnval.r
    cR
    crg
    elex
    va
    cR
    vb
    va
    cv
    #
    cbs
    cfv
    #
    cpw
    #
    @10
    vt
    @16
    csubrg
    cfv
    #
    crab
    #
    cint
    #
    cmpt
    @13
    cvv
    crgspn
    @16
    cR
    wceq
    #
    vb
    @18
    @21
    @8
    @12
    @22
    @17
    @7
    @16
    cR
    cbs
    fveq2
    pweqd
    @22
    @20
    @11
    @22
    @19
    @4
    wceq
    @20
    @11
    wceq
    @16
    cR
    csubrg
    fveq2
    @10
    vt
    @19
    @4
    rabeq
    syl
    inteqd
    mpteq12dv
    va
    vt
    vb
    df-rgspn
    vb
    @8
    @12
    @7
    cR
    cbs
    fvex
    #
    pwex
    mptex
    fvmpt
    3syl
    fveq1d
    wph
    cA
    @8
    wcel
    #
    @6
    cvv
    wcel
    #
    @14
    @6
    wceq
    wph
    cA
    @7
    wss
    @24
    wph
    cA
    cB
    @7
    rgspnval.ss
    rgspnval.b
    sseqtrd
    cA
    @7
    @23
    elpw2
    sylibr
    wph
    @3
    vt
    @4
    wrex
    #
    @25
    wph
    cB
    @4
    wcel
    cA
    cB
    wss
    #
    @26
    wph
    cB
    @7
    @4
    rgspnval.b
    wph
    @15
    @7
    @4
    wcel
    rgspnval.r
    @7
    cR
    @7
    eqid
    subrgid
    syl
    eqeltrd
    rgspnval.ss
    @3
    @27
    vt
    cB
    @4
    @2
    cB
    cA
    sseq2
    rspcev
    syl2anc
    @3
    vt
    @4
    intexrab
    sylib
    vb
    cA
    @12
    @6
    @8
    cvv
    @13
    @9
    cA
    wceq
    #
    @11
    @5
    @28
    @10
    @3
    vt
    @4
    @9
    cA
    @2
    sseq1
    rabbidv
    inteqd
    @13
    eqid
    fvmptg
    syl2anc
    eqtrd
    3eqtrd
end
