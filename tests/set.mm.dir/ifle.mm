include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "wi.mm"
include "wa.mm"
include "cif.mm"
include "simpll1.mm"
include "leidd.mm"
include "wceq.mm"
include "iftrue.mm"
include "adantl.mm"
include "id.mm"
include "imp.mm"
include "adantll.mm"
include "iftrued.mm"
include "3brtr4d.mm"
include "wn.mm"
include "iffalse.mm"
include "simpll3.mm"
include "simpll2.mm"
include "breq2.mm"
include "ifboth.mm"
include "syl2anc.mm"
include "eqbrtrd.mm"
include "pm2.61dan.mm"

theorem ifle
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR /\ B e. RR /\ B <_ A ) /\ ( ph -> ps ) ) -> if ( ph , A , B ) <_ if ( ps , A , B ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cB
    cA
    cle
    wbr
    #
    w3a
    #
    wph
    wps
    wi
    #
    wa
    #
    wph
    wph
    cA
    cB
    cif
    #
    wps
    cA
    cB
    cif
    #
    cle
    wbr
    @5
    wph
    wa
    #
    cA
    cA
    @6
    @7
    cle
    @8
    cA
    @0
    @1
    @2
    @4
    wph
    simpll1
    leidd
    wph
    @6
    cA
    wceq
    @5
    wph
    cA
    cB
    iftrue
    adantl
    @8
    wps
    cA
    cB
    @4
    wph
    wps
    @3
    @4
    wph
    wps
    @4
    id
    imp
    adantll
    iftrued
    3brtr4d
    @5
    wph
    wn
    #
    wa
    #
    @6
    cB
    @7
    cle
    @9
    @6
    cB
    wceq
    @5
    wph
    cA
    cB
    iffalse
    adantl
    @10
    @2
    cB
    cB
    cle
    wbr
    #
    cB
    @7
    cle
    wbr
    #
    @0
    @1
    @2
    @4
    @9
    simpll3
    @10
    cB
    @0
    @1
    @2
    @4
    @9
    simpll2
    leidd
    wps
    @2
    @11
    @12
    cA
    cB
    cA
    @7
    cB
    cle
    breq2
    cB
    @7
    cB
    cle
    breq2
    ifboth
    syl2anc
    eqbrtrd
    pm2.61dan
end
