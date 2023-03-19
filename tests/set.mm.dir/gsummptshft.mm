include "cfz.mm"
include "co.mm"
include "cmpt.mm"
include "cgsu.mm"
include "caddc.mm"
include "cv.mm"
include "cmin.mm"
include "ccom.mm"
include "cvv.mm"
include "ovexd.mm"
include "eqid.mm"
include "fmptd.mm"
include "fzfid.mm"
include "wcel.mm"
include "c0g.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "fsuppmptdm.mm"
include "mptfzshft.mm"
include "gsumf1o.mm"
include "wa.mm"
include "cc.mm"
include "wceq.mm"
include "elfzelz.mm"
include "zcnd.mm"
include "npcan.mm"
include "syl2anr.mm"
include "simpr.mm"
include "eqeltrd.mm"
include "cz.mm"
include "wb.mm"
include "jca.mm"
include "adantr.mm"
include "adantl.mm"
include "zsubcld.mm"
include "fzaddel.mm"
include "syl12anc.mm"
include "mpbird.mm"
include "eqidd.mm"
include "fmptco.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem gsummptshft
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vj: setvar j
  let vk: setvar k
  let cG: class G
  let cK: class K
  let cM: class M
  let cN: class N
  let c.0: class .0.
  assume gsummptshft.b: |- B = ( Base ` G )
  assume gsummptshft.z: |- .0. = ( 0g ` G )
  assume gsummptshft.g: |- ( ph -> G e. CMnd )
  assume gsummptshft.k: |- ( ph -> K e. ZZ )
  assume gsummptshft.m: |- ( ph -> M e. ZZ )
  assume gsummptshft.n: |- ( ph -> N e. ZZ )
  assume gsummptshft.a: |- ( ( ph /\ j e. ( M ... N ) ) -> A e. B )
  assume gsummptshft.c: |- ( j = ( k - K ) -> A = C )

  disjoint A k
  disjoint B j
  disjoint C j
  disjoint j k
  disjoint K j
  disjoint K k
  disjoint M j
  disjoint M k
  disjoint N j
  disjoint N k
  disjoint j ph
  disjoint k ph
  assert |- ( ph -> ( G gsum ( j e. ( M ... N ) |-> A ) ) = ( G gsum ( k e. ( ( M + K ) ... ( N + K ) ) |-> C ) ) )

  proof
    wph
    cG
    vj
    cM
    cN
    cfz
    co
    #
    cA
    cmpt
    #
    cgsu
    co
    cG
    @1
    vk
    cM
    cK
    caddc
    co
    #
    cN
    cK
    caddc
    co
    #
    cfz
    co
    #
    vk
    cv
    #
    cK
    cmin
    co
    #
    cmpt
    #
    ccom
    #
    cgsu
    co
    cG
    vk
    @4
    cC
    cmpt
    #
    cgsu
    co
    wph
    @0
    cB
    @4
    @1
    cG
    @7
    cvv
    c.0
    gsummptshft.b
    gsummptshft.z
    gsummptshft.g
    wph
    cM
    cN
    cfz
    ovexd
    wph
    vj
    @0
    cA
    cB
    @1
    gsummptshft.a
    @1
    eqid
    #
    fmptd
    wph
    vj
    @0
    @1
    cB
    cvv
    cA
    c.0
    @10
    wph
    cM
    cN
    fzfid
    gsummptshft.a
    c.0
    cvv
    wcel
    wph
    c.0
    cG
    c0g
    cfv
    cvv
    gsummptshft.z
    cG
    c0g
    fvex
    eqeltri
    a1i
    fsuppmptdm
    wph
    vk
    cK
    cM
    cN
    gsummptshft.k
    gsummptshft.m
    gsummptshft.n
    mptfzshft
    gsumf1o
    wph
    @8
    @9
    cG
    cgsu
    wph
    vk
    vj
    @4
    @0
    @6
    cA
    cC
    @7
    @1
    wph
    @5
    @4
    wcel
    #
    wa
    #
    @6
    @0
    wcel
    #
    @6
    cK
    caddc
    co
    #
    @4
    wcel
    #
    @12
    @14
    @5
    @4
    @11
    @5
    cc
    wcel
    cK
    cc
    wcel
    @14
    @5
    wceq
    wph
    @11
    @5
    @5
    @2
    @3
    elfzelz
    #
    zcnd
    wph
    cK
    gsummptshft.k
    zcnd
    @5
    cK
    npcan
    syl2anr
    wph
    @11
    simpr
    eqeltrd
    @12
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    @6
    cz
    wcel
    cK
    cz
    wcel
    #
    @13
    @15
    wb
    wph
    @19
    @11
    wph
    @17
    @18
    gsummptshft.m
    gsummptshft.n
    jca
    adantr
    @12
    @5
    cK
    @11
    @5
    cz
    wcel
    wph
    @16
    adantl
    wph
    @20
    @11
    gsummptshft.k
    adantr
    #
    zsubcld
    @21
    @6
    cK
    cM
    cN
    fzaddel
    syl12anc
    mpbird
    wph
    @7
    eqidd
    wph
    @1
    eqidd
    gsummptshft.c
    fmptco
    oveq2d
    eqtrd
end
