include "cfz.mm"
include "co.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cplusg.mm"
include "cfv.mm"
include "cseq.mm"
include "cmnd.mm"
include "eqid.mm"
include "fmptd.mm"
include "gsumval2.mm"
include "cv.mm"
include "ffvelrnda.mm"
include "wcel.mm"
include "wa.mm"
include "adantr.mm"
include "simprl.mm"
include "simprr.mm"
include "mndcl.mm"
include "syl3anc.mm"
include "seqcl.mm"
include "eqeltrd.mm"

theorem gsumncl
  let wph: wff ph
  let cB: class B
  let cP: class P
  let vk: setvar k
  let cK: class K
  let cM: class M
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  assume gsumncl.k: |- K = ( Base ` M )
  assume gsumncl.w: |- ( ph -> M e. Mnd )
  assume gsumncl.p: |- ( ph -> P e. ( ZZ>= ` N ) )
  assume gsumncl.b: |- ( ( ph /\ k e. ( N ... P ) ) -> B e. K )

  disjoint K k
  disjoint N k
  disjoint P k
  disjoint k ph
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint k x
  disjoint k y
  disjoint K x
  disjoint K y
  disjoint M x
  disjoint M y
  disjoint N x
  disjoint N y
  disjoint P x
  disjoint P y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( M gsum ( k e. ( N ... P ) |-> B ) ) e. K )

  proof
    wph
    cM
    vk
    cN
    cP
    cfz
    co
    #
    cB
    cmpt
    #
    cgsu
    co
    cP
    cM
    cplusg
    cfv
    #
    @1
    cN
    cseq
    cfv
    cK
    wph
    cK
    @2
    @1
    cM
    cN
    cP
    cmnd
    gsumncl.k
    @2
    eqid
    #
    gsumncl.w
    gsumncl.p
    wph
    vk
    @0
    cB
    cK
    @1
    gsumncl.b
    @1
    eqid
    fmptd
    #
    gsumval2
    wph
    vx
    vy
    @2
    cK
    @1
    cN
    cP
    gsumncl.p
    wph
    @0
    cK
    vx
    cv
    #
    @1
    @4
    ffvelrnda
    wph
    @5
    cK
    wcel
    #
    vy
    cv
    #
    cK
    wcel
    #
    wa
    #
    wa
    cM
    cmnd
    wcel
    #
    @6
    @8
    @5
    @7
    @2
    co
    cK
    wcel
    wph
    @10
    @9
    gsumncl.w
    adantr
    wph
    @6
    @8
    simprl
    wph
    @6
    @8
    simprr
    cK
    @2
    cM
    @5
    @7
    gsumncl.k
    @3
    mndcl
    syl3anc
    seqcl
    eqeltrd
end
