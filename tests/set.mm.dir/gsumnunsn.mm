include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "cmpt.mm"
include "cseq.mm"
include "cfv.mm"
include "cgsu.mm"
include "cuz.mm"
include "wcel.mm"
include "wceq.mm"
include "seqp1.mm"
include "syl.mm"
include "cmnd.mm"
include "peano2uz.mm"
include "cv.mm"
include "wa.mm"
include "adantlr.mm"
include "ad2antrr.mm"
include "eqeltrd.mm"
include "wo.mm"
include "wb.mm"
include "elfzp1.mm"
include "biimpa.mm"
include "mpjaodan.mm"
include "eqid.mm"
include "fmptd.mm"
include "gsumval2.mm"
include "cres.mm"
include "wss.mm"
include "fzssp1.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "fveq1i.mm"
include "fvres.mm"
include "adantl.mm"
include "syl5reqr.mm"
include "seqfveq.mm"
include "eqtr4d.mm"
include "eqidd.mm"
include "eluzfz2.mm"
include "fvmptd.mm"
include "eqcomd.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"

theorem gsumnunsn
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cP: class P
  let c.pl: class .+
  let vk: setvar k
  let cK: class K
  let cM: class M
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  let vi: setvar i
  assume gsumncl.k: |- K = ( Base ` M )
  assume gsumncl.w: |- ( ph -> M e. Mnd )
  assume gsumncl.p: |- ( ph -> P e. ( ZZ>= ` N ) )
  assume gsumncl.b: |- ( ( ph /\ k e. ( N ... P ) ) -> B e. K )
  assume gsumnunsn.a: |- .+ = ( +g ` M )
  assume gsumnunsn.l: |- ( ph -> C e. K )
  assume gsumnunsn.c: |- ( ( ph /\ k = ( P + 1 ) ) -> B = C )

  disjoint K k
  disjoint N k
  disjoint P k
  disjoint k ph
  disjoint C k
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
  disjoint B i
  disjoint i k
  disjoint N i
  disjoint P i
  disjoint i ph
  assert |- ( ph -> ( M gsum ( k e. ( N ... ( P + 1 ) ) |-> B ) ) = ( ( M gsum ( k e. ( N ... P ) |-> B ) ) .+ C ) )

  proof
    wph
    cP
    c1
    caddc
    co
    #
    c.pl
    vk
    cN
    @0
    cfz
    co
    #
    cB
    cmpt
    #
    cN
    cseq
    #
    cfv
    #
    cP
    @3
    cfv
    #
    @0
    @2
    cfv
    #
    c.pl
    co
    #
    cM
    @2
    cgsu
    co
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
    #
    cC
    c.pl
    co
    wph
    cP
    cN
    cuz
    cfv
    #
    wcel
    #
    @4
    @7
    wceq
    gsumncl.p
    c.pl
    @2
    cN
    cP
    seqp1
    syl
    wph
    cK
    c.pl
    @2
    cM
    cN
    @0
    cmnd
    gsumncl.k
    gsumnunsn.a
    gsumncl.w
    wph
    @12
    @0
    @11
    wcel
    #
    gsumncl.p
    cN
    cP
    peano2uz
    syl
    #
    wph
    vk
    @1
    cB
    cK
    @2
    wph
    vk
    cv
    #
    @1
    wcel
    #
    wa
    #
    @15
    @8
    wcel
    #
    cB
    cK
    wcel
    #
    @15
    @0
    wceq
    #
    wph
    @18
    @19
    @16
    gsumncl.b
    adantlr
    @17
    @20
    wa
    cB
    cC
    cK
    wph
    @20
    cB
    cC
    wceq
    @16
    gsumnunsn.c
    adantlr
    wph
    cC
    cK
    wcel
    @16
    @20
    gsumnunsn.l
    ad2antrr
    eqeltrd
    wph
    @16
    @18
    @20
    wo
    #
    wph
    @12
    @16
    @21
    wb
    gsumncl.p
    @15
    cN
    cP
    elfzp1
    syl
    biimpa
    mpjaodan
    @2
    eqid
    fmptd
    gsumval2
    wph
    @10
    @5
    cC
    @6
    c.pl
    wph
    @10
    cP
    c.pl
    @9
    cN
    cseq
    cfv
    @5
    wph
    cK
    c.pl
    @9
    cM
    cN
    cP
    cmnd
    gsumncl.k
    gsumnunsn.a
    gsumncl.w
    gsumncl.p
    wph
    vk
    @8
    cB
    cK
    @9
    gsumncl.b
    @9
    eqid
    fmptd
    gsumval2
    wph
    c.pl
    vi
    @2
    @9
    cN
    cP
    gsumncl.p
    wph
    vi
    cv
    #
    @8
    wcel
    #
    wa
    @22
    @9
    cfv
    @22
    @2
    @8
    cres
    #
    cfv
    #
    @22
    @2
    cfv
    #
    @22
    @24
    @9
    @8
    @1
    wss
    @24
    @9
    wceq
    cN
    cP
    fzssp1
    vk
    @1
    @8
    cB
    resmpt
    ax-mp
    fveq1i
    @23
    @25
    @26
    wceq
    wph
    @22
    @8
    @2
    fvres
    adantl
    syl5reqr
    seqfveq
    eqtr4d
    wph
    @6
    cC
    wph
    vk
    @0
    cB
    cC
    @1
    @2
    cK
    wph
    @2
    eqidd
    gsumnunsn.c
    wph
    @13
    @0
    @1
    wcel
    @14
    cN
    @0
    eluzfz2
    syl
    gsumnunsn.l
    fvmptd
    eqcomd
    oveq12d
    3eqtr4d
end
