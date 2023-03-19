include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "c0.mm"
include "wceq.mm"
include "cc0.mm"
include "cv.mm"
include "wrex.mm"
include "cab.mm"
include "clt.mm"
include "csup.mm"
include "cif.mm"
include "iftrue.mm"
include "0red.mm"
include "eqeltrd.mm"
include "adantl.mm"
include "wn.mm"
include "wa.mm"
include "simpr.mm"
include "iffalsed.mm"
include "neqned.mm"
include "adantlr.mm"
include "adantr.mm"
include "eqid.mm"
include "upbdrech.mm"
include "simpld.mm"
include "pm2.61dan.mm"
include "syl5eqel.mm"
include "rzal.mm"
include "simprd.mm"
include "wb.mm"
include "iffalse.mm"
include "syl5eq.mm"
include "breq2d.mm"
include "ralbidv.mm"
include "mpbird.mm"
include "jca.mm"

theorem upbdrech2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  assume upbdrech2.b: |- ( ( ph /\ x e. A ) -> B e. RR )
  assume upbdrech2.bd: |- ( ph -> E. y e. RR A. x e. A B <_ y )
  assume upbdrech2.c: |- C = if ( A = (/) , 0 , sup ( { z | E. x e. A z = B } , RR , < ) )

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( C e. RR /\ A. x e. A B <_ C ) )

  proof
    wph
    cC
    cr
    wcel
    cB
    cC
    cle
    wbr
    #
    vx
    cA
    wral
    #
    wph
    cC
    cA
    c0
    wceq
    #
    cc0
    vz
    cv
    cB
    wceq
    vx
    cA
    wrex
    vz
    cab
    cr
    clt
    csup
    #
    cif
    #
    cr
    upbdrech2.c
    wph
    @2
    @4
    cr
    wcel
    #
    @2
    @5
    wph
    @2
    @4
    cc0
    cr
    @2
    cc0
    @3
    iftrue
    @2
    0red
    eqeltrd
    adantl
    wph
    @2
    wn
    #
    wa
    #
    @4
    @3
    cr
    @7
    @2
    cc0
    @3
    wph
    @6
    simpr
    #
    iffalsed
    @7
    @3
    cr
    wcel
    #
    cB
    @3
    cle
    wbr
    #
    vx
    cA
    wral
    #
    @7
    vx
    vy
    vz
    cA
    cB
    @3
    @7
    cA
    c0
    @8
    neqned
    wph
    vx
    cv
    cA
    wcel
    cB
    cr
    wcel
    @6
    upbdrech2.b
    adantlr
    wph
    cB
    vy
    cv
    cle
    wbr
    vx
    cA
    wral
    vy
    cr
    wrex
    @6
    upbdrech2.bd
    adantr
    @3
    eqid
    upbdrech
    #
    simpld
    eqeltrd
    pm2.61dan
    syl5eqel
    wph
    @2
    @1
    @2
    @1
    wph
    @0
    vx
    cA
    rzal
    adantl
    @7
    @1
    @11
    @7
    @9
    @11
    @12
    simprd
    @6
    @1
    @11
    wb
    wph
    @6
    @0
    @10
    vx
    cA
    @6
    cC
    @3
    cB
    cle
    @6
    cC
    @4
    @3
    upbdrech2.c
    @2
    cc0
    @3
    iffalse
    syl5eq
    breq2d
    ralbidv
    adantl
    mpbird
    pm2.61dan
    jca
end
