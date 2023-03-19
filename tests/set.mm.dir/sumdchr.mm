include "cv.mm"
include "cfv.mm"
include "csu.mm"
include "wceq.mm"
include "chash.mm"
include "cc0.mm"
include "cif.mm"
include "cphi.mm"
include "sumdchr2.mm"
include "cn.mm"
include "wcel.mm"
include "dchrhash.mm"
include "syl.mm"
include "ifeq1d.mm"
include "eqtrd.mm"

theorem sumdchr
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let c.1: class .1.
  let cG: class G
  let cN: class N
  let cZ: class Z
  let vy: setvar y
  let vz: setvar z
  let va: setvar a
  let vb: setvar b
  assume sumdchr.g: |- G = ( DChr ` N )
  assume sumdchr.d: |- D = ( Base ` G )
  assume sumdchr.z: |- Z = ( Z/nZ ` N )
  assume sumdchr.1: |- .1. = ( 1r ` Z )
  assume sumdchr.b: |- B = ( Base ` Z )
  assume sumdchr.n: |- ( ph -> N e. NN )
  assume sumdchr.a: |- ( ph -> A e. B )

  disjoint .1. x
  disjoint A x
  disjoint D x
  disjoint N x
  disjoint G x
  disjoint ph x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint .1. y
  disjoint .1. z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint D a
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint D b
  disjoint D y
  disjoint D z
  disjoint N a
  disjoint N y
  disjoint G a
  disjoint G b
  disjoint G y
  disjoint G z
  disjoint ph y
  disjoint ph z
  disjoint Z y
  assert |- ( ph -> sum_ x e. D ( x ` A ) = if ( A = .1. , ( phi ` N ) , 0 ) )

  proof
    wph
    cD
    cA
    vx
    cv
    cfv
    vx
    csu
    cA
    c.1
    wceq
    #
    cD
    chash
    cfv
    #
    cc0
    cif
    @0
    cN
    cphi
    cfv
    #
    cc0
    cif
    wph
    vx
    cA
    cB
    cD
    c.1
    cG
    cN
    cZ
    sumdchr.g
    sumdchr.d
    sumdchr.z
    sumdchr.1
    sumdchr.b
    sumdchr.n
    sumdchr.a
    sumdchr2
    wph
    @0
    @1
    @2
    cc0
    wph
    cN
    cn
    wcel
    @1
    @2
    wceq
    sumdchr.n
    cD
    cG
    cN
    sumdchr.g
    sumdchr.d
    dchrhash
    syl
    ifeq1d
    eqtrd
end
