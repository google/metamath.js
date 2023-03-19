include "cc0.mm"
include "c1.mm"
include "cneg.mm"
include "caddc.mm"
include "co.mm"
include "1pneg1e0.mm"
include "cmul.mm"
include "neg1mulneg1e1.mm"
include "caovcld.mm"
include "syl5eqelr.mm"

theorem plydivlem1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let vz: setvar z
  let cA: class A
  let vd: setvar d
  let vf: setvar f
  let vp: setvar p
  let vq: setvar q
  let cF: class F
  let cH: class H
  let cB: class B
  let cD: class D
  let cM: class M
  let cN: class N
  let cT: class T
  let vg: setvar g
  let vw: setvar w
  let cG: class G
  let cR: class R
  assume plydiv.pl: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x + y ) e. S )
  assume plydiv.tm: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x x. y ) e. S )
  assume plydiv.rc: |- ( ( ph /\ ( x e. S /\ x =/= 0 ) ) -> ( 1 / x ) e. S )
  assume plydiv.m1: |- ( ph -> -u 1 e. S )

  disjoint x y
  disjoint ph x
  disjoint ph y
  disjoint S x
  disjoint S y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint d f
  disjoint d p
  disjoint d q
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint F d
  disjoint f p
  disjoint f q
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint F f
  disjoint p q
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint F p
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint F q
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint H f
  disjoint H p
  disjoint H q
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint d ph
  disjoint ph z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint D f
  disjoint D z
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint N f
  disjoint N p
  disjoint N q
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint T x
  disjoint T y
  disjoint d g
  disjoint d w
  disjoint G d
  disjoint f g
  disjoint f w
  disjoint G f
  disjoint g p
  disjoint g q
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint G g
  disjoint p w
  disjoint G p
  disjoint q w
  disjoint G q
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint R d
  disjoint R f
  disjoint R p
  disjoint R x
  disjoint R y
  disjoint S d
  disjoint S f
  disjoint S g
  disjoint S p
  disjoint S q
  disjoint S z
  assert |- ( ph -> 0 e. S )

  proof
    wph
    cc0
    c1
    c1
    cneg
    #
    caddc
    co
    cS
    1pneg1e0
    wph
    vx
    vy
    c1
    @0
    cS
    cS
    cS
    caddc
    plydiv.pl
    wph
    c1
    @0
    @0
    cmul
    co
    cS
    neg1mulneg1e1
    wph
    vx
    vy
    @0
    @0
    cS
    cS
    cS
    cmul
    plydiv.tm
    plydiv.m1
    plydiv.m1
    caovcld
    syl5eqelr
    plydiv.m1
    caovcld
    syl5eqelr
end
