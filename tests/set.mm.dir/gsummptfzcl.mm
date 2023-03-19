include "cmpt.mm"
include "cgsu.mm"
include "co.mm"
include "cplusg.mm"
include "cfv.mm"
include "cseq.mm"
include "cmnd.mm"
include "eqid.mm"
include "wcel.mm"
include "wral.mm"
include "cfz.mm"
include "wf.mm"
include "fmpt.mm"
include "feq2d.mm"
include "syl5bb.mm"
include "mpbid.mm"
include "gsumval2.mm"
include "cv.mm"
include "wa.mm"
include "adantr.mm"
include "sylib.mm"
include "eqcomd.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "ffvelrnd.mm"
include "simprl.mm"
include "simprr.mm"
include "mndcl.mm"
include "syl3anc.mm"
include "seqcl.mm"
include "eqeltrd.mm"

theorem gsummptfzcl
  let wph: wff ph
  let cB: class B
  let vi: setvar i
  let cG: class G
  let cI: class I
  let cM: class M
  let cN: class N
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume gsummptfzcl.b: |- B = ( Base ` G )
  assume gsummptfzcl.g: |- ( ph -> G e. Mnd )
  assume gsummptfzcl.n: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume gsummptfzcl.i: |- ( ph -> I = ( M ... N ) )
  assume gsummptfzcl.e: |- ( ph -> A. i e. I X e. B )

  disjoint I i
  disjoint B i
  disjoint i x
  disjoint i y
  disjoint x y
  disjoint I x
  disjoint I y
  disjoint B x
  disjoint B y
  disjoint G x
  disjoint G y
  disjoint M x
  disjoint M y
  disjoint N x
  disjoint N y
  disjoint X x
  disjoint X y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( G gsum ( i e. I |-> X ) ) e. B )

  proof
    wph
    cG
    vi
    cI
    cX
    cmpt
    #
    cgsu
    co
    cN
    cG
    cplusg
    cfv
    #
    @0
    cM
    cseq
    cfv
    cB
    wph
    cB
    @1
    @0
    cG
    cM
    cN
    cmnd
    gsummptfzcl.b
    @1
    eqid
    #
    gsummptfzcl.g
    gsummptfzcl.n
    wph
    cX
    cB
    wcel
    vi
    cI
    wral
    #
    cM
    cN
    cfz
    co
    #
    cB
    @0
    wf
    #
    gsummptfzcl.e
    @3
    cI
    cB
    @0
    wf
    #
    wph
    @5
    vi
    cI
    cB
    cX
    @0
    @0
    eqid
    fmpt
    #
    wph
    cI
    @4
    cB
    @0
    gsummptfzcl.i
    feq2d
    syl5bb
    mpbid
    gsumval2
    wph
    vx
    vy
    @1
    cB
    @0
    cM
    cN
    gsummptfzcl.n
    wph
    vx
    cv
    #
    @4
    wcel
    #
    wa
    #
    cI
    cB
    @8
    @0
    @10
    @3
    @6
    wph
    @3
    @9
    gsummptfzcl.e
    adantr
    @7
    sylib
    wph
    @9
    @8
    cI
    wcel
    wph
    @4
    cI
    @8
    wph
    cI
    @4
    gsummptfzcl.i
    eqcomd
    eleq2d
    biimpa
    ffvelrnd
    wph
    @8
    cB
    wcel
    #
    vy
    cv
    #
    cB
    wcel
    #
    wa
    #
    wa
    cG
    cmnd
    wcel
    #
    @11
    @13
    @8
    @12
    @1
    co
    cB
    wcel
    wph
    @15
    @14
    gsummptfzcl.g
    adantr
    wph
    @11
    @13
    simprl
    wph
    @11
    @13
    simprr
    cB
    @1
    cG
    @8
    @12
    gsummptfzcl.b
    @2
    mndcl
    syl3anc
    seqcl
    eqeltrd
end
