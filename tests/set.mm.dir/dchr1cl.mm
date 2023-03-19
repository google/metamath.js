include "cv.mm"
include "wcel.mm"
include "c1.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "wceq.mm"
include "eqidd.mm"
include "cmulr.mm"
include "cfv.mm"
include "co.mm"
include "cur.mm"
include "wa.mm"
include "1cnd.mm"
include "cmul.mm"
include "1t1e1.mm"
include "eqcomi.mm"
include "a1i.mm"
include "dchrelbasd.mm"
include "syl5eqel.mm"

theorem dchr1cl
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cU: class U
  let c.1: class .1.
  let vk: setvar k
  let cG: class G
  let cN: class N
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let cK: class K
  let cL: class L
  let cA: class A
  let cX: class X
  let cY: class Y
  assume dchrmhm.g: |- G = ( DChr ` N )
  assume dchrmhm.z: |- Z = ( Z/nZ ` N )
  assume dchrmhm.b: |- D = ( Base ` G )
  assume dchrn0.b: |- B = ( Base ` Z )
  assume dchrn0.u: |- U = ( Unit ` Z )
  assume dchr1cl.o: |- .1. = ( k e. B |-> if ( k e. U , 1 , 0 ) )
  assume dchr1cl.n: |- ( ph -> N e. NN )

  disjoint B k
  disjoint U k
  disjoint N k
  disjoint k ph
  disjoint Z k
  disjoint x y
  disjoint .1. x
  disjoint .1. y
  disjoint k x
  disjoint k y
  disjoint B x
  disjoint B y
  disjoint K x
  disjoint K y
  disjoint L x
  disjoint L y
  disjoint U x
  disjoint U y
  disjoint A x
  disjoint N x
  disjoint N y
  disjoint ph x
  disjoint ph y
  disjoint X k
  disjoint X x
  disjoint X y
  disjoint Z x
  disjoint Z y
  disjoint D x
  disjoint Y x
  disjoint Y y
  assert |- ( ph -> .1. e. D )

  proof
    wph
    c.1
    vk
    cB
    vk
    cv
    #
    cU
    wcel
    #
    c1
    cc0
    cif
    cmpt
    cD
    dchr1cl.o
    wph
    vx
    vy
    c1
    cB
    c1
    cD
    cU
    vk
    c1
    cG
    cN
    c1
    c1
    cZ
    dchrmhm.g
    dchrmhm.z
    dchrn0.b
    dchrn0.u
    dchr1cl.n
    dchrmhm.b
    @0
    vx
    cv
    #
    wceq
    c1
    eqidd
    @0
    vy
    cv
    #
    wceq
    c1
    eqidd
    @0
    @2
    @3
    cZ
    cmulr
    cfv
    co
    wceq
    c1
    eqidd
    @0
    cZ
    cur
    cfv
    wceq
    c1
    eqidd
    wph
    @1
    wa
    1cnd
    c1
    c1
    c1
    cmul
    co
    #
    wceq
    wph
    @2
    cU
    wcel
    @3
    cU
    wcel
    wa
    wa
    @4
    c1
    1t1e1
    eqcomi
    a1i
    wph
    c1
    eqidd
    dchrelbasd
    syl5eqel
end
