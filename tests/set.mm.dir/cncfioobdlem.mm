include "cv.mm"
include "wceq.mm"
include "cfv.mm"
include "cif.mm"
include "cicc.mm"
include "co.mm"
include "cmpt.mm"
include "a1i.mm"
include "wa.mm"
include "cr.mm"
include "wcel.mm"
include "adantr.mm"
include "clt.mm"
include "wbr.mm"
include "cioo.mm"
include "w3a.mm"
include "cxr.mm"
include "wb.mm"
include "rexrd.mm"
include "elioo2.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "simp2d.mm"
include "eqcom.mm"
include "biimpi.mm"
include "adantl.mm"
include "breqtrd.mm"
include "gtned.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "simpr.mm"
include "elioored.mm"
include "eqeltrd.mm"
include "simp3d.mm"
include "eqbrtrd.mm"
include "ltned.mm"
include "fveq2d.mm"
include "3eqtrd.mm"
include "ioossicc.mm"
include "sseldi.mm"
include "ffvelrnd.mm"
include "fvmptd.mm"

theorem cncfioobdlem
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cF: class F
  let cG: class G
  let cL: class L
  let cV: class V
  let vk: setvar k
  assume cncfioobdlem.a: |- ( ph -> A e. RR )
  assume cncfioobdlem.b: |- ( ph -> B e. RR )
  assume cncfioobdlem.f: |- ( ph -> F : ( A (,) B ) --> V )
  assume cncfioobdlem.g: |- G = ( x e. ( A [,] B ) |-> if ( x = A , R , if ( x = B , L , ( F ` x ) ) ) )
  assume cncfioobdlem.c: |- ( ph -> C e. ( A (,) B ) )

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint F x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( G ` C ) = ( F ` C ) )

  proof
    wph
    vx
    cC
    vx
    cv
    #
    cA
    wceq
    #
    cR
    @0
    cB
    wceq
    #
    cL
    @0
    cF
    cfv
    #
    cif
    #
    cif
    #
    cC
    cF
    cfv
    #
    cA
    cB
    cicc
    co
    #
    cG
    cV
    cG
    vx
    @7
    @5
    cmpt
    wceq
    wph
    cncfioobdlem.g
    a1i
    wph
    @0
    cC
    wceq
    #
    wa
    #
    @5
    @4
    @3
    @6
    @9
    @1
    cR
    @4
    @9
    @0
    cA
    @9
    cA
    @0
    wph
    cA
    cr
    wcel
    @8
    cncfioobdlem.a
    adantr
    @9
    cA
    cC
    @0
    clt
    wph
    cA
    cC
    clt
    wbr
    #
    @8
    wph
    cC
    cr
    wcel
    #
    @10
    cC
    cB
    clt
    wbr
    #
    wph
    cC
    cA
    cB
    cioo
    co
    #
    wcel
    #
    @11
    @10
    @12
    w3a
    #
    cncfioobdlem.c
    wph
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    @14
    @15
    wb
    wph
    cA
    cncfioobdlem.a
    rexrd
    wph
    cB
    cncfioobdlem.b
    rexrd
    cA
    cB
    cC
    elioo2
    syl2anc
    mpbid
    #
    simp2d
    adantr
    @8
    cC
    @0
    wceq
    #
    wph
    @8
    @17
    @0
    cC
    eqcom
    biimpi
    adantl
    breqtrd
    gtned
    neneqd
    iffalsed
    @9
    @2
    cL
    @3
    @9
    @0
    cB
    @9
    @0
    cB
    @9
    @0
    cC
    cr
    wph
    @8
    simpr
    #
    wph
    @11
    @8
    wph
    cC
    cA
    cB
    cncfioobdlem.c
    elioored
    adantr
    eqeltrd
    @9
    @0
    cC
    cB
    clt
    @18
    wph
    @12
    @8
    wph
    @11
    @10
    @12
    @16
    simp3d
    adantr
    eqbrtrd
    ltned
    neneqd
    iffalsed
    @9
    @0
    cC
    cF
    @18
    fveq2d
    3eqtrd
    wph
    @13
    @7
    cC
    cA
    cB
    ioossicc
    cncfioobdlem.c
    sseldi
    wph
    @13
    cV
    cC
    cF
    cncfioobdlem.f
    cncfioobdlem.c
    ffvelrnd
    fvmptd
end
