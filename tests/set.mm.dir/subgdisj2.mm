include "cin.mm"
include "csn.mm"
include "incom.mm"
include "syl5eqr.mm"
include "cntzrecd.mm"
include "co.mm"
include "cfv.mm"
include "wcel.mm"
include "wceq.mm"
include "sseldd.mm"
include "cntzi.mm"
include "syl2anc.mm"
include "3eqtr3d.mm"
include "subgdisj1.mm"

theorem subgdisj2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let cT: class T
  let cU: class U
  let cG: class G
  let c.0: class .0.
  let cZ: class Z
  assume subgdisj.p: |- .+ = ( +g ` G )
  assume subgdisj.o: |- .0. = ( 0g ` G )
  assume subgdisj.z: |- Z = ( Cntz ` G )
  assume subgdisj.t: |- ( ph -> T e. ( SubGrp ` G ) )
  assume subgdisj.u: |- ( ph -> U e. ( SubGrp ` G ) )
  assume subgdisj.i: |- ( ph -> ( T i^i U ) = { .0. } )
  assume subgdisj.s: |- ( ph -> T C_ ( Z ` U ) )
  assume subgdisj.a: |- ( ph -> A e. T )
  assume subgdisj.c: |- ( ph -> C e. T )
  assume subgdisj.b: |- ( ph -> B e. U )
  assume subgdisj.d: |- ( ph -> D e. U )
  assume subgdisj.j: |- ( ph -> ( A .+ B ) = ( C .+ D ) )


  assert |- ( ph -> B = D )

  proof
    wph
    cB
    cA
    cD
    cC
    c.pl
    cU
    cT
    cG
    c.0
    cZ
    subgdisj.p
    subgdisj.o
    subgdisj.z
    subgdisj.u
    subgdisj.t
    wph
    cU
    cT
    cin
    cT
    cU
    cin
    c.0
    csn
    cT
    cU
    incom
    subgdisj.i
    syl5eqr
    wph
    cT
    cU
    cG
    cZ
    subgdisj.z
    subgdisj.t
    subgdisj.u
    subgdisj.s
    cntzrecd
    subgdisj.b
    subgdisj.d
    subgdisj.a
    subgdisj.c
    wph
    cA
    cB
    c.pl
    co
    #
    cC
    cD
    c.pl
    co
    #
    cB
    cA
    c.pl
    co
    #
    cD
    cC
    c.pl
    co
    #
    subgdisj.j
    wph
    cA
    cU
    cZ
    cfv
    #
    wcel
    cB
    cU
    wcel
    @0
    @2
    wceq
    wph
    cT
    @4
    cA
    subgdisj.s
    subgdisj.a
    sseldd
    subgdisj.b
    c.pl
    cU
    cG
    cA
    cB
    cZ
    subgdisj.p
    subgdisj.z
    cntzi
    syl2anc
    wph
    cC
    @4
    wcel
    cD
    cU
    wcel
    @1
    @3
    wceq
    wph
    cT
    @4
    cC
    subgdisj.s
    subgdisj.c
    sseldd
    subgdisj.d
    c.pl
    cU
    cG
    cC
    cD
    cZ
    subgdisj.p
    subgdisj.z
    cntzi
    syl2anc
    3eqtr3d
    subgdisj1
end
