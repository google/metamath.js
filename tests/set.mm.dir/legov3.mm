include "co.mm"
include "wbr.mm"
include "wceq.mm"
include "wo.mm"
include "wne.mm"
include "wa.mm"
include "ltgov.mm"
include "orbi1d.mm"
include "simprl.mm"
include "legid.mm"
include "adantr.mm"
include "simpr.mm"
include "breqtrd.mm"
include "adantlr.mm"
include "mpjaodan.mm"
include "wn.mm"
include "simplr.mm"
include "neqned.mm"
include "jca.mm"
include "ex.mm"
include "orrd.mm"
include "orcomd.mm"
include "impbida.mm"
include "bitr2d.mm"

theorem legov3
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let c.lt: class .<
  let cE: class E
  let cG: class G
  let cI: class I
  let c.le: class .<_
  let c.mi: class .-
  let va: setvar a
  let vx: setvar x
  let vy: setvar y
  assume legval.p: |- P = ( Base ` G )
  assume legval.d: |- .- = ( dist ` G )
  assume legval.i: |- I = ( Itv ` G )
  assume legval.l: |- .<_ = ( leG ` G )
  assume legval.g: |- ( ph -> G e. TarskiG )
  assume legso.a: |- E = ( .- " ( P X. P ) )
  assume legso.f: |- ( ph -> Fun .- )
  assume legso.l: |- .< = ( ( .<_ |` E ) \ _I )
  assume legso.d: |- ( ph -> ( P X. P ) C_ dom .- )
  assume ltgov.a: |- ( ph -> A e. P )
  assume ltgov.b: |- ( ph -> B e. P )


  assert |- ( ph -> ( ( A .- B ) .<_ ( C .- D ) <-> ( ( A .- B ) .< ( C .- D ) \/ ( A .- B ) = ( C .- D ) ) ) )

  proof
    wph
    cA
    cB
    c.mi
    co
    #
    cC
    cD
    c.mi
    co
    #
    c.lt
    wbr
    #
    @0
    @1
    wceq
    #
    wo
    @0
    @1
    c.le
    wbr
    #
    @0
    @1
    wne
    #
    wa
    #
    @3
    wo
    #
    @4
    wph
    @2
    @6
    @3
    wph
    cA
    cB
    cC
    cD
    cP
    c.lt
    cE
    cG
    cI
    c.le
    c.mi
    legval.p
    legval.d
    legval.i
    legval.l
    legval.g
    legso.a
    legso.f
    legso.l
    legso.d
    ltgov.a
    ltgov.b
    ltgov
    orbi1d
    wph
    @7
    @4
    wph
    @7
    wa
    #
    @6
    @4
    @3
    @8
    @4
    @5
    simprl
    wph
    @3
    @4
    @7
    wph
    @3
    wa
    @0
    @0
    @1
    c.le
    wph
    @0
    @0
    c.le
    wbr
    @3
    wph
    cA
    cB
    cP
    cG
    cI
    c.le
    c.mi
    legval.p
    legval.d
    legval.i
    legval.l
    legval.g
    ltgov.a
    ltgov.b
    legid
    adantr
    wph
    @3
    simpr
    breqtrd
    adantlr
    wph
    @7
    simpr
    mpjaodan
    wph
    @4
    wa
    #
    @3
    @6
    @9
    @3
    @6
    @9
    @3
    wn
    #
    @6
    @9
    @10
    wa
    #
    @4
    @5
    wph
    @4
    @10
    simplr
    @11
    @0
    @1
    @9
    @10
    simpr
    neqned
    jca
    ex
    orrd
    orcomd
    impbida
    bitr2d
end
