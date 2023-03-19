include "cr.mm"
include "clt.mm"
include "csup.mm"
include "cv.mm"
include "cneg.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cmin.mm"
include "a1i.mm"
include "wcel.mm"
include "wa.mm"
include "sselda.mm"
include "recnd.mm"
include "cc.mm"
include "adantr.mm"
include "negsubd.mm"
include "eqcomd.mm"
include "eqeq2d.mm"
include "rexbidva.mm"
include "abbidv.mm"
include "eqidd.mm"
include "3eqtrd.mm"
include "supeq1d.mm"
include "renegcld.mm"
include "eqid.mm"
include "supaddc.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "suprcl.mm"
include "syl3anc.mm"
include "3eqtrrd.mm"

theorem supsubc
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cC: class C
  assume supsubc.a1: |- ( ph -> A C_ RR )
  assume supsubc.a2: |- ( ph -> A =/= (/) )
  assume supsubc.a3: |- ( ph -> E. x e. RR A. y e. A y <_ x )
  assume supsubc.b: |- ( ph -> B e. RR )
  assume supsubc.c: |- C = { z | E. v e. A z = ( v - B ) }

  disjoint A v
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B v
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint ph v
  disjoint ph z
  assert |- ( ph -> ( sup ( A , RR , < ) - B ) = sup ( C , RR , < ) )

  proof
    wph
    cC
    cr
    clt
    csup
    vz
    cv
    #
    vv
    cv
    #
    cB
    cneg
    #
    caddc
    co
    #
    wceq
    #
    vv
    cA
    wrex
    #
    vz
    cab
    #
    cr
    clt
    csup
    #
    cA
    cr
    clt
    csup
    #
    @2
    caddc
    co
    #
    @8
    cB
    cmin
    co
    wph
    cr
    cC
    @6
    clt
    wph
    cC
    @0
    @1
    cB
    cmin
    co
    #
    wceq
    #
    vv
    cA
    wrex
    #
    vz
    cab
    #
    @6
    @6
    cC
    @13
    wceq
    wph
    supsubc.c
    a1i
    wph
    @12
    @5
    vz
    wph
    @11
    @4
    vv
    cA
    wph
    @1
    cA
    wcel
    #
    wa
    #
    @10
    @3
    @0
    @15
    @3
    @10
    @15
    @1
    cB
    @15
    @1
    wph
    cA
    cr
    @1
    supsubc.a1
    sselda
    recnd
    wph
    cB
    cc
    wcel
    @14
    wph
    cB
    supsubc.b
    recnd
    #
    adantr
    negsubd
    eqcomd
    eqeq2d
    rexbidva
    abbidv
    wph
    @6
    eqidd
    3eqtrd
    supeq1d
    wph
    @9
    @7
    wph
    vx
    vy
    vz
    vv
    cA
    @2
    @6
    supsubc.a1
    supsubc.a2
    supsubc.a3
    wph
    cB
    supsubc.b
    renegcld
    @6
    eqid
    supaddc
    eqcomd
    wph
    @8
    cB
    wph
    @8
    wph
    cA
    cr
    wss
    cA
    c0
    wne
    vy
    cv
    vx
    cv
    cle
    wbr
    vy
    cA
    wral
    vx
    cr
    wrex
    @8
    cr
    wcel
    supsubc.a1
    supsubc.a2
    supsubc.a3
    vx
    vy
    cA
    suprcl
    syl3anc
    recnd
    @16
    negsubd
    3eqtrrd
end
