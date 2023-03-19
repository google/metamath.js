include "co.mm"
include "wbr.mm"
include "wcel.mm"
include "cid.mm"
include "wn.mm"
include "wa.mm"
include "wne.mm"
include "cres.mm"
include "cdif.mm"
include "breqi.mm"
include "brdif.mm"
include "bitri.mm"
include "ovex.mm"
include "brres.mm"
include "anbi1i.mm"
include "anass.mm"
include "3bitri.mm"
include "ideq.mm"
include "necon3bbii.mm"
include "cxp.mm"
include "cima.mm"
include "elovimad.mm"
include "syl6eleqr.mm"
include "biantrurd.mm"
include "syl5rbbr.mm"
include "anbi2d.mm"
include "syl5bb.mm"

theorem ltgov
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


  assert |- ( ph -> ( ( A .- B ) .< ( C .- D ) <-> ( ( A .- B ) .<_ ( C .- D ) /\ ( A .- B ) =/= ( C .- D ) ) ) )

  proof
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
    c.le
    wbr
    #
    @0
    cE
    wcel
    #
    @0
    @1
    cid
    wbr
    #
    wn
    #
    wa
    #
    wa
    #
    wph
    @3
    @0
    @1
    wne
    #
    wa
    @2
    @0
    @1
    c.le
    cE
    cres
    #
    wbr
    #
    @6
    wa
    #
    @3
    @4
    wa
    #
    @6
    wa
    @8
    @2
    @0
    @1
    @10
    cid
    cdif
    #
    wbr
    @12
    @0
    @1
    c.lt
    @14
    legso.l
    breqi
    @0
    @1
    @10
    cid
    brdif
    bitri
    @11
    @13
    @6
    @0
    @1
    c.le
    cE
    cC
    cD
    c.mi
    ovex
    #
    brres
    anbi1i
    @3
    @4
    @6
    anass
    3bitri
    wph
    @7
    @9
    @3
    @9
    @6
    wph
    @7
    @5
    @0
    @1
    @0
    @1
    @15
    ideq
    necon3bbii
    wph
    @4
    @6
    wph
    @0
    c.mi
    cP
    cP
    cxp
    cima
    cE
    wph
    cA
    cB
    cP
    cP
    c.mi
    ltgov.a
    ltgov.b
    legso.f
    legso.d
    elovimad
    legso.a
    syl6eleqr
    biantrurd
    syl5rbbr
    anbi2d
    syl5bb
end
