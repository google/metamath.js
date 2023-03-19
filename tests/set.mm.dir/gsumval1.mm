include "cgsu.mm"
include "co.mm"
include "crn.mm"
include "wss.mm"
include "cfz.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "cseq.mm"
include "cfv.mm"
include "wa.mm"
include "cuz.mm"
include "wrex.mm"
include "wex.mm"
include "cio.mm"
include "c1.mm"
include "ccnv.mm"
include "cvv.mm"
include "cdif.mm"
include "cima.mm"
include "chash.mm"
include "wf1o.mm"
include "ccom.mm"
include "cif.mm"
include "eqidd.mm"
include "wf.mm"
include "wral.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "fss.mm"
include "sylancl.mm"
include "gsumval.mm"
include "frn.mm"
include "iftrue.mm"
include "3syl.mm"
include "eqtrd.mm"

theorem gsumval1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cF: class F
  let cG: class G
  let cO: class O
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  let vz: setvar z
  assume gsumval1.b: |- B = ( Base ` G )
  assume gsumval1.z: |- .0. = ( 0g ` G )
  assume gsumval1.p: |- .+ = ( +g ` G )
  assume gsumval1.o: |- O = { x e. B | A. y e. B ( ( x .+ y ) = y /\ ( y .+ x ) = y ) }
  assume gsumval1.g: |- ( ph -> G e. V )
  assume gsumval1.a: |- ( ph -> A e. W )
  assume gsumval1.f: |- ( ph -> F : A --> O )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint .+ x
  disjoint .+ y
  disjoint f m
  disjoint f n
  disjoint f z
  disjoint F f
  disjoint m n
  disjoint m z
  disjoint F m
  disjoint n z
  disjoint F n
  disjoint F z
  disjoint G f
  disjoint G m
  disjoint G n
  disjoint G z
  disjoint O f
  disjoint O m
  disjoint O n
  disjoint O z
  disjoint f ph
  disjoint m ph
  disjoint n ph
  disjoint ph z
  disjoint x z
  disjoint y z
  disjoint B z
  disjoint .+ z
  assert |- ( ph -> ( G gsum F ) = .0. )

  proof
    wph
    cG
    cF
    cgsu
    co
    cF
    crn
    cO
    wss
    #
    c.0
    cA
    cfz
    crn
    wcel
    cA
    vm
    cv
    #
    vn
    cv
    #
    cfz
    co
    wceq
    vz
    cv
    #
    @2
    c.pl
    cF
    @1
    cseq
    cfv
    wceq
    wa
    vn
    @1
    cuz
    cfv
    wrex
    vm
    wex
    vz
    cio
    c1
    cF
    ccnv
    cvv
    cO
    cdif
    cima
    #
    chash
    cfv
    #
    cfz
    co
    @4
    vf
    cv
    #
    wf1o
    @3
    @5
    c.pl
    cF
    @6
    ccom
    c1
    cseq
    cfv
    wceq
    wa
    vf
    wex
    vz
    cio
    cif
    #
    cif
    #
    c.0
    wph
    vz
    vy
    cA
    cB
    c.pl
    vf
    vm
    vn
    cF
    cG
    cO
    cV
    @4
    cW
    c.0
    vx
    gsumval1.b
    gsumval1.z
    gsumval1.p
    gsumval1.o
    wph
    @4
    eqidd
    gsumval1.g
    gsumval1.a
    wph
    cA
    cO
    cF
    wf
    #
    cO
    cB
    wss
    cA
    cB
    cF
    wf
    gsumval1.f
    cO
    vx
    cv
    #
    vy
    cv
    #
    c.pl
    co
    @11
    wceq
    @11
    @10
    c.pl
    co
    @11
    wceq
    wa
    vy
    cB
    wral
    #
    vx
    cB
    crab
    cB
    gsumval1.o
    @12
    vx
    cB
    ssrab2
    eqsstri
    cA
    cO
    cB
    cF
    fss
    sylancl
    gsumval
    wph
    @9
    @0
    @8
    c.0
    wceq
    gsumval1.f
    cA
    cO
    cF
    frn
    @0
    c.0
    @7
    iftrue
    3syl
    eqtrd
end
