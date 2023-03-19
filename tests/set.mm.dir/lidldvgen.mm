include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "csn.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "wbr.mm"
include "wral.mm"
include "wa.mm"
include "wss.mm"
include "simp1.mm"
include "simp3.mm"
include "snssd.mm"
include "rspssid.mm"
include "syl2anc.mm"
include "wb.mm"
include "snssg.mm"
include "3ad2ant3.mm"
include "mpbird.mm"
include "cab.mm"
include "rspsn.mm"
include "3adant2.mm"
include "eleq2d.mm"
include "vex.mm"
include "breq2.mm"
include "elab.mm"
include "syl6bb.mm"
include "biimpd.mm"
include "ralrimiv.mm"
include "jca.mm"
include "eleq2.mm"
include "raleq.mm"
include "anbi12d.mm"
include "syl5ibrcom.mm"
include "wi.mm"
include "wal.mm"
include "df-ral.mm"
include "ssab.mm"
include "bitr4i.mm"
include "biimpi.mm"
include "ad2antll.mm"
include "adantr.mm"
include "sseqtr4d.mm"
include "simpl1.mm"
include "simpl2.mm"
include "snssi.mm"
include "adantl.mm"
include "rspssp.mm"
include "syl3anc.mm"
include "adantrr.mm"
include "eqssd.mm"
include "ex.mm"
include "impbid.mm"

theorem lidldvgen
  let vx: setvar x
  let cB: class B
  let c.pa: class .||
  let cR: class R
  let cU: class U
  let cG: class G
  let cI: class I
  let cK: class K
  let vy: setvar y
  assume lidldvgen.b: |- B = ( Base ` R )
  assume lidldvgen.u: |- U = ( LIdeal ` R )
  assume lidldvgen.k: |- K = ( RSpan ` R )
  assume lidldvgen.d: |- .|| = ( ||r ` R )

  disjoint U x
  disjoint B x
  disjoint .|| x
  disjoint R x
  disjoint I x
  disjoint K x
  disjoint G x
  disjoint U y
  disjoint x y
  disjoint B y
  disjoint .|| y
  disjoint R y
  disjoint I y
  disjoint K y
  disjoint G y
  assert |- ( ( R e. Ring /\ I e. U /\ G e. B ) -> ( I = ( K ` { G } ) <-> ( G e. I /\ A. x e. I G .|| x ) ) )

  proof
    cR
    crg
    wcel
    #
    cI
    cU
    wcel
    #
    cG
    cB
    wcel
    #
    w3a
    #
    cI
    cG
    csn
    #
    cK
    cfv
    #
    wceq
    #
    cG
    cI
    wcel
    #
    cG
    vx
    cv
    #
    c.pa
    wbr
    #
    vx
    cI
    wral
    #
    wa
    #
    @3
    @11
    @6
    cG
    @5
    wcel
    #
    @9
    vx
    @5
    wral
    #
    wa
    @3
    @12
    @13
    @3
    @12
    @4
    @5
    wss
    #
    @3
    @0
    @4
    cB
    wss
    @14
    @0
    @1
    @2
    simp1
    @3
    cG
    cB
    @0
    @1
    @2
    simp3
    snssd
    cB
    cR
    @4
    cK
    lidldvgen.k
    lidldvgen.b
    rspssid
    syl2anc
    @2
    @0
    @12
    @14
    wb
    @1
    cG
    @5
    cB
    snssg
    3ad2ant3
    mpbird
    @3
    @9
    vx
    @5
    @3
    @8
    @5
    wcel
    #
    @9
    @3
    @15
    @8
    cG
    vy
    cv
    #
    c.pa
    wbr
    #
    vy
    cab
    #
    wcel
    @9
    @3
    @5
    @18
    @8
    @0
    @2
    @5
    @18
    wceq
    @1
    vy
    cB
    c.pa
    cR
    cG
    cK
    lidldvgen.b
    lidldvgen.k
    lidldvgen.d
    rspsn
    3adant2
    eleq2d
    @17
    @9
    vy
    @8
    vx
    vex
    @16
    @8
    cG
    c.pa
    breq2
    elab
    syl6bb
    biimpd
    ralrimiv
    jca
    @6
    @7
    @12
    @10
    @13
    cI
    @5
    cG
    eleq2
    @9
    vx
    cI
    @5
    raleq
    anbi12d
    syl5ibrcom
    @3
    @11
    @6
    @3
    @11
    wa
    #
    cI
    @5
    @19
    cI
    @9
    vx
    cab
    #
    @5
    @10
    cI
    @20
    wss
    #
    @3
    @7
    @10
    @21
    @10
    @8
    cI
    wcel
    @9
    wi
    vx
    wal
    @21
    @9
    vx
    cI
    df-ral
    @9
    vx
    cI
    ssab
    bitr4i
    biimpi
    ad2antll
    @3
    @5
    @20
    wceq
    #
    @11
    @0
    @2
    @22
    @1
    vx
    cB
    c.pa
    cR
    cG
    cK
    lidldvgen.b
    lidldvgen.k
    lidldvgen.d
    rspsn
    3adant2
    adantr
    sseqtr4d
    @3
    @7
    @5
    cI
    wss
    #
    @10
    @3
    @7
    wa
    @0
    @1
    @4
    cI
    wss
    #
    @23
    @0
    @1
    @2
    @7
    simpl1
    @0
    @1
    @2
    @7
    simpl2
    @7
    @24
    @3
    cG
    cI
    snssi
    adantl
    cR
    cU
    @4
    cI
    cK
    lidldvgen.k
    lidldvgen.u
    rspssp
    syl3anc
    adantrr
    eqssd
    ex
    impbid
end
