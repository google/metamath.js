include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cfv.mm"
include "cz.mm"
include "csn.mm"
include "cxp.mm"
include "cuz.mm"
include "eqid.mm"
include "eluzelz.mm"
include "eleq2s.mm"
include "adantl.mm"
include "cli.mm"
include "wbr.mm"
include "adantr.mm"
include "cc.mm"
include "c1.mm"
include "cr.mm"
include "ffvelrnda.mm"
include "recnd.mm"
include "1z.mm"
include "uzssz.mm"
include "zex.mm"
include "climconst2.mm"
include "sylancl.mm"
include "cv.mm"
include "wf.mm"
include "ad2antrr.mm"
include "uztrn2.mm"
include "adantll.mm"
include "ffvelrnd.mm"
include "wceq.mm"
include "fvex.mm"
include "fvconst2.mm"
include "syl.mm"
include "eqeltrd.mm"
include "cle.mm"
include "simpr.mm"
include "cfz.mm"
include "co.mm"
include "simplr.mm"
include "elfzuz.mm"
include "syl2an.mm"
include "caddc.mm"
include "cmin.mm"
include "simpl.mm"
include "adantlr.mm"
include "syldan.mm"
include "monoord2.mm"
include "breqtrrd.mm"
include "climle.mm"

theorem iseraltlem1
  let wph: wff ph
  let vk: setvar k
  let cG: class G
  let cM: class M
  let cN: class N
  let cZ: class Z
  let vj: setvar j
  let vn: setvar n
  let vx: setvar x
  let cF: class F
  let cK: class K
  assume iseralt.1: |- Z = ( ZZ>= ` M )
  assume iseralt.2: |- ( ph -> M e. ZZ )
  assume iseralt.3: |- ( ph -> G : Z --> RR )
  assume iseralt.4: |- ( ( ph /\ k e. Z ) -> ( G ` ( k + 1 ) ) <_ ( G ` k ) )
  assume iseralt.5: |- ( ph -> G ~~> 0 )

  disjoint G k
  disjoint M k
  disjoint k ph
  disjoint N k
  disjoint Z k
  disjoint j k
  disjoint j n
  disjoint j x
  disjoint F j
  disjoint k n
  disjoint k x
  disjoint F k
  disjoint n x
  disjoint F n
  disjoint F x
  disjoint G j
  disjoint G n
  disjoint G x
  disjoint M j
  disjoint M n
  disjoint M x
  disjoint j ph
  disjoint n ph
  disjoint ph x
  disjoint K k
  disjoint K x
  disjoint N n
  disjoint N x
  disjoint Z j
  disjoint Z n
  disjoint Z x
  assert |- ( ( ph /\ N e. Z ) -> 0 <_ ( G ` N ) )

  proof
    wph
    cN
    cZ
    wcel
    #
    wa
    #
    cc0
    cN
    cG
    cfv
    #
    vn
    cG
    cz
    @2
    csn
    cxp
    #
    cN
    cN
    cuz
    cfv
    #
    @4
    eqid
    @0
    cN
    cz
    wcel
    #
    wph
    @5
    cN
    cM
    cuz
    cfv
    cZ
    cM
    cN
    eluzelz
    iseralt.1
    eleq2s
    adantl
    wph
    cG
    cc0
    cli
    wbr
    @0
    iseralt.5
    adantr
    @1
    @2
    cc
    wcel
    c1
    cz
    wcel
    @3
    @2
    cli
    wbr
    @1
    @2
    wph
    cZ
    cr
    cN
    cG
    iseralt.3
    ffvelrnda
    #
    recnd
    1z
    @2
    c1
    cz
    c1
    uzssz
    zex
    climconst2
    sylancl
    @1
    vn
    cv
    #
    @4
    wcel
    #
    wa
    #
    cZ
    cr
    @7
    cG
    wph
    cZ
    cr
    cG
    wf
    #
    @0
    @8
    iseralt.3
    ad2antrr
    #
    @0
    @8
    @7
    cZ
    wcel
    wph
    cM
    @7
    cN
    cZ
    iseralt.1
    uztrn2
    adantll
    ffvelrnd
    @9
    @7
    @3
    cfv
    #
    @2
    cr
    @9
    @7
    cz
    wcel
    #
    @12
    @2
    wceq
    @8
    @13
    @1
    cN
    @7
    eluzelz
    adantl
    cz
    @2
    @7
    cN
    cG
    fvex
    fvconst2
    syl
    #
    @1
    @2
    cr
    wcel
    @8
    @6
    adantr
    eqeltrd
    @9
    @7
    cG
    cfv
    @2
    @12
    cle
    @9
    vk
    cG
    cN
    @7
    @1
    @8
    simpr
    @9
    vk
    cv
    #
    cN
    @7
    cfz
    co
    wcel
    #
    wa
    cZ
    cr
    @15
    cG
    @9
    @10
    @16
    @11
    adantr
    @9
    @0
    @15
    @4
    wcel
    #
    @15
    cZ
    wcel
    #
    @16
    wph
    @0
    @8
    simplr
    @15
    cN
    @7
    elfzuz
    cM
    @15
    cN
    cZ
    iseralt.1
    uztrn2
    #
    syl2an
    ffvelrnd
    @9
    @1
    @17
    @15
    c1
    caddc
    co
    cG
    cfv
    @15
    cG
    cfv
    cle
    wbr
    #
    @15
    cN
    @7
    c1
    cmin
    co
    #
    cfz
    co
    wcel
    @1
    @8
    simpl
    @15
    cN
    @21
    elfzuz
    @1
    @17
    @18
    @20
    @0
    @17
    @18
    wph
    @19
    adantll
    wph
    @18
    @20
    @0
    iseralt.4
    adantlr
    syldan
    syl2an
    monoord2
    @14
    breqtrrd
    climle
end
