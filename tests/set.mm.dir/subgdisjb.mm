include "co.mm"
include "wceq.mm"
include "wa.mm"
include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "adantr.mm"
include "cin.mm"
include "csn.mm"
include "wss.mm"
include "simpr.mm"
include "subgdisj1.mm"
include "subgdisj2.mm"
include "jca.mm"
include "ex.mm"
include "oveq12.mm"
include "impbid1.mm"

theorem subgdisjb
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


  assert |- ( ph -> ( ( A .+ B ) = ( C .+ D ) <-> ( A = C /\ B = D ) ) )

  proof
    wph
    cA
    cB
    c.pl
    co
    cC
    cD
    c.pl
    co
    wceq
    #
    cA
    cC
    wceq
    #
    cB
    cD
    wceq
    #
    wa
    #
    wph
    @0
    @3
    wph
    @0
    wa
    #
    @1
    @2
    @4
    cA
    cB
    cC
    cD
    c.pl
    cT
    cU
    cG
    c.0
    cZ
    subgdisj.p
    subgdisj.o
    subgdisj.z
    wph
    cT
    cG
    csubg
    cfv
    #
    wcel
    @0
    subgdisj.t
    adantr
    #
    wph
    cU
    @5
    wcel
    @0
    subgdisj.u
    adantr
    #
    wph
    cT
    cU
    cin
    c.0
    csn
    wceq
    @0
    subgdisj.i
    adantr
    #
    wph
    cT
    cU
    cZ
    cfv
    wss
    @0
    subgdisj.s
    adantr
    #
    wph
    cA
    cT
    wcel
    @0
    subgdisj.a
    adantr
    #
    wph
    cC
    cT
    wcel
    @0
    subgdisj.c
    adantr
    #
    wph
    cB
    cU
    wcel
    @0
    subgdisj.b
    adantr
    #
    wph
    cD
    cU
    wcel
    @0
    subgdisj.d
    adantr
    #
    wph
    @0
    simpr
    #
    subgdisj1
    @4
    cA
    cB
    cC
    cD
    c.pl
    cT
    cU
    cG
    c.0
    cZ
    subgdisj.p
    subgdisj.o
    subgdisj.z
    @6
    @7
    @8
    @9
    @10
    @11
    @12
    @13
    @14
    subgdisj2
    jca
    ex
    cA
    cC
    cB
    cD
    c.pl
    oveq12
    impbid1
end
