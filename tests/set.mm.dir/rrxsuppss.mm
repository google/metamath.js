include "cdm.mm"
include "cc0.mm"
include "csupp.mm"
include "co.mm"
include "suppssdm.mm"
include "cr.mm"
include "wf.mm"
include "wceq.mm"
include "rrxf.mm"
include "fdm.mm"
include "syl.mm"
include "syl5sseq.mm"

theorem rrxsuppss
  let wph: wff ph
  let vh: setvar h
  let cF: class F
  let cI: class I
  let cX: class X
  let cA: class A
  let vk: setvar k
  let cD: class D
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cG: class G
  let cV: class V
  assume rrxmval.1: |- X = { h e. ( RR ^m I ) | h finSupp 0 }
  assume rrxf.1: |- ( ph -> F e. X )

  disjoint F h
  disjoint I h
  disjoint A k
  disjoint D f
  disjoint D g
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F f
  disjoint F g
  disjoint F k
  disjoint F x
  disjoint f h
  disjoint f k
  disjoint g h
  disjoint g k
  disjoint h k
  disjoint h x
  disjoint k x
  disjoint G f
  disjoint G g
  disjoint G h
  disjoint G k
  disjoint G x
  disjoint I f
  disjoint I g
  disjoint I k
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint h y
  disjoint h z
  disjoint k y
  disjoint k z
  disjoint V f
  disjoint V g
  disjoint V h
  disjoint V k
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint X f
  disjoint X g
  disjoint X k
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( ph -> ( F supp 0 ) C_ I )

  proof
    wph
    cF
    cdm
    #
    cF
    cc0
    csupp
    co
    cI
    cF
    cc0
    suppssdm
    wph
    cI
    cr
    cF
    wf
    @0
    cI
    wceq
    wph
    vh
    cF
    cI
    cX
    rrxmval.1
    rrxf.1
    rrxf
    cI
    cr
    cF
    fdm
    syl
    syl5sseq
end
