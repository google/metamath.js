include "covol.mm"
include "cfv.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "ovolscalem2.mm"
include "c1.mm"
include "cmul.mm"
include "recnd.mm"
include "rpcnd.mm"
include "rpne0d.mm"
include "divrecd.mm"
include "cv.mm"
include "wcel.mm"
include "cr.mm"
include "crab.mm"
include "ssrab2.mm"
include "syl6eqss.mm"
include "rpreccld.mm"
include "sca2rab.mm"
include "wss.mm"
include "rerpdivcld.mm"
include "ovollecl.mm"
include "syl3anc.mm"
include "lemuldivd.mm"
include "mpbird.mm"
include "eqbrtrd.mm"
include "letri3d.mm"
include "mpbir2and.mm"

theorem ovolsca
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let vk: setvar k
  let vn: setvar n
  let vy: setvar y
  let cF: class F
  let cG: class G
  let cR: class R
  let vm: setvar m
  let cS: class S
  assume ovolsca.1: |- ( ph -> A C_ RR )
  assume ovolsca.2: |- ( ph -> C e. RR+ )
  assume ovolsca.3: |- ( ph -> B = { x e. RR | ( C x. x ) e. A } )
  assume ovolsca.4: |- ( ph -> ( vol* ` A ) e. RR )

  disjoint A x
  disjoint C x
  disjoint f k
  disjoint f n
  disjoint f x
  disjoint f y
  disjoint A f
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint x y
  disjoint A y
  disjoint B f
  disjoint B n
  disjoint B y
  disjoint F n
  disjoint F x
  disjoint G k
  disjoint G n
  disjoint G y
  disjoint R k
  disjoint R x
  disjoint R y
  disjoint f m
  disjoint C f
  disjoint k m
  disjoint C k
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint C m
  disjoint C n
  disjoint C y
  disjoint f ph
  disjoint k ph
  disjoint n ph
  disjoint ph y
  disjoint S k
  disjoint S x
  assert |- ( ph -> ( vol* ` B ) = ( ( vol* ` A ) / C ) )

  proof
    wph
    cB
    covol
    cfv
    #
    cA
    covol
    cfv
    #
    cC
    cdiv
    co
    #
    wceq
    @0
    @2
    cle
    wbr
    #
    @2
    @0
    cle
    wbr
    wph
    vx
    cA
    cB
    cC
    ovolsca.1
    ovolsca.2
    ovolsca.3
    ovolsca.4
    ovolscalem2
    #
    wph
    @2
    @1
    c1
    cC
    cdiv
    co
    #
    cmul
    co
    #
    @0
    cle
    wph
    @1
    cC
    wph
    @1
    ovolsca.4
    recnd
    wph
    cC
    ovolsca.2
    rpcnd
    wph
    cC
    ovolsca.2
    rpne0d
    divrecd
    wph
    @6
    @0
    cle
    wbr
    @1
    @0
    @5
    cdiv
    co
    cle
    wbr
    wph
    vy
    cB
    cA
    @5
    wph
    cB
    cC
    vx
    cv
    cmul
    co
    cA
    wcel
    #
    vx
    cr
    crab
    cr
    ovolsca.3
    @7
    vx
    cr
    ssrab2
    syl6eqss
    #
    wph
    cC
    ovolsca.2
    rpreccld
    #
    wph
    vx
    vy
    cA
    cB
    cC
    ovolsca.1
    ovolsca.2
    ovolsca.3
    sca2rab
    wph
    cB
    cr
    wss
    @2
    cr
    wcel
    @3
    @0
    cr
    wcel
    @8
    wph
    @1
    cC
    ovolsca.4
    ovolsca.2
    rerpdivcld
    #
    @4
    cB
    @2
    ovollecl
    syl3anc
    #
    ovolscalem2
    wph
    @1
    @0
    @5
    ovolsca.4
    @11
    @9
    lemuldivd
    mpbird
    eqbrtrd
    wph
    @0
    @2
    @11
    @10
    letri3d
    mpbir2and
end
