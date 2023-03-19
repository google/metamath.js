include "cmnd.mm"
include "wcel.mm"
include "wa.mm"
include "wn.mm"
include "w3a.mm"
include "wo.mm"
include "cif.mm"
include "co.mm"
include "wceq.mm"
include "pm2.21.mm"
include "imp.mm"
include "3ad2antl3.mm"
include "mndrid.mm"
include "3adant3.mm"
include "adantr.mm"
include "iftrue.mm"
include "iffalse.mm"
include "oveqan12d.mm"
include "adantl.mm"
include "orcs.mm"
include "ad2antrl.mm"
include "3eqtr4rd.mm"
include "mndlid.mm"
include "olcs.mm"
include "ad2antll.mm"
include "simp1.mm"
include "mndidcl.mm"
include "syl.mm"
include "syl2anc.mm"
include "ioran.mm"
include "sylbir.mm"
include "4casesdan.mm"

theorem mndifsplit
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cM: class M
  let c.0: class .0.
  assume mndifsplit.b: |- B = ( Base ` M )
  assume mndifsplit.0g: |- .0. = ( 0g ` M )
  assume mndifsplit.pg: |- .+ = ( +g ` M )


  assert |- ( ( M e. Mnd /\ A e. B /\ -. ( ph /\ ps ) ) -> if ( ( ph \/ ps ) , A , .0. ) = ( if ( ph , A , .0. ) .+ if ( ps , A , .0. ) ) )

  proof
    cM
    cmnd
    wcel
    #
    cA
    cB
    wcel
    #
    wph
    wps
    wa
    #
    wn
    #
    w3a
    #
    wph
    wps
    wph
    wps
    wo
    #
    cA
    c.0
    cif
    #
    wph
    cA
    c.0
    cif
    #
    wps
    cA
    c.0
    cif
    #
    c.pl
    co
    #
    wceq
    #
    @3
    @0
    @2
    @10
    @1
    @3
    @2
    @10
    @2
    @10
    pm2.21
    imp
    3ad2antl3
    @4
    wph
    wps
    wn
    #
    wa
    #
    wa
    cA
    c.0
    c.pl
    co
    #
    cA
    @9
    @6
    @4
    @13
    cA
    wceq
    #
    @12
    @0
    @1
    @14
    @3
    cB
    c.pl
    cM
    cA
    c.0
    mndifsplit.b
    mndifsplit.pg
    mndifsplit.0g
    mndrid
    3adant3
    adantr
    @12
    @9
    @13
    wceq
    @4
    wph
    @11
    @7
    cA
    @8
    c.0
    c.pl
    wph
    cA
    c.0
    iftrue
    wps
    cA
    c.0
    iffalse
    #
    oveqan12d
    adantl
    wph
    @6
    cA
    wceq
    #
    @4
    @11
    wph
    wps
    @16
    @5
    cA
    c.0
    iftrue
    #
    orcs
    ad2antrl
    3eqtr4rd
    @4
    wph
    wn
    #
    wps
    wa
    #
    wa
    c.0
    cA
    c.pl
    co
    #
    cA
    @9
    @6
    @4
    @20
    cA
    wceq
    #
    @19
    @0
    @1
    @21
    @3
    cB
    c.pl
    cM
    cA
    c.0
    mndifsplit.b
    mndifsplit.pg
    mndifsplit.0g
    mndlid
    3adant3
    adantr
    @19
    @9
    @20
    wceq
    @4
    @18
    wps
    @7
    c.0
    @8
    cA
    c.pl
    wph
    cA
    c.0
    iffalse
    #
    wps
    cA
    c.0
    iftrue
    oveqan12d
    adantl
    wps
    @16
    @4
    @18
    wph
    wps
    @16
    @17
    olcs
    ad2antll
    3eqtr4rd
    @4
    @18
    @11
    wa
    #
    wa
    c.0
    c.0
    c.pl
    co
    #
    c.0
    @9
    @6
    @4
    @24
    c.0
    wceq
    #
    @23
    @4
    @0
    c.0
    cB
    wcel
    #
    @25
    @0
    @1
    @3
    simp1
    #
    @4
    @0
    @26
    @27
    cB
    cM
    c.0
    mndifsplit.b
    mndifsplit.0g
    mndidcl
    syl
    cB
    c.pl
    cM
    c.0
    c.0
    mndifsplit.b
    mndifsplit.pg
    mndifsplit.0g
    mndlid
    syl2anc
    adantr
    @23
    @9
    @24
    wceq
    @4
    @18
    @11
    @7
    c.0
    @8
    c.0
    c.pl
    @22
    @15
    oveqan12d
    adantl
    @23
    @6
    c.0
    wceq
    #
    @4
    @23
    @5
    wn
    @28
    wph
    wps
    ioran
    @5
    cA
    c.0
    iffalse
    sylbir
    adantl
    3eqtr4rd
    4casesdan
end
