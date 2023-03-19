include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "idn1.mm"
include "simpl.mm"
include "e1a.mm"
include "simpr.mm"
include "pm3.2.mm"
include "e11.mm"
include "in1.mm"
include "eximi.mm"
include "jca.mm"
include "wsb.mm"
include "wb.mm"
include "biimpi.mm"
include "dfvd1ir.mm"
include "wal.mm"
include "wn.mm"
include "wo.mm"
include "2eximi.mm"
include "ax6e2ndeq.mm"
include "biimpri.mm"
include "2sb5nd.mm"
include "biimpr.mm"
include "com12.mm"
include "sban.mm"
include "sbbii.mm"
include "bitri.mm"
include "simplbi2comt.mm"
include "com13.mm"
include "e110.mm"
include "biimp.mm"
include "sylbir.mm"
include "impbii.mm"

theorem 2uasbanhVD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u
  assume 2uasbanhVD.1: |- ( ch <-> ( E. x E. y ( ( x = u /\ y = v ) /\ ph ) /\ E. x E. y ( ( x = u /\ y = v ) /\ ps ) ) )

  disjoint u x
  disjoint u y
  disjoint v x
  disjoint v y
  assert |- ( E. x E. y ( ( x = u /\ y = v ) /\ ( ph /\ ps ) ) <-> ( E. x E. y ( ( x = u /\ y = v ) /\ ph ) /\ E. x E. y ( ( x = u /\ y = v ) /\ ps ) ) )

  proof
    vx
    cv
    #
    vu
    cv
    #
    wceq
    vy
    cv
    #
    vv
    cv
    #
    wceq
    wa
    #
    wph
    wps
    wa
    #
    wa
    #
    vy
    wex
    #
    vx
    wex
    #
    @4
    wph
    wa
    #
    vy
    wex
    #
    vx
    wex
    #
    @4
    wps
    wa
    #
    vy
    wex
    #
    vx
    wex
    #
    wa
    #
    @8
    @11
    @14
    @7
    @10
    vx
    @6
    @9
    vy
    @6
    @9
    @6
    @4
    wph
    @9
    @6
    @6
    @4
    @6
    idn1
    #
    @4
    @5
    simpl
    e1a
    #
    @6
    @5
    wph
    @6
    @6
    @5
    @16
    @4
    @5
    simpr
    e1a
    #
    wph
    wps
    simpl
    e1a
    @4
    wph
    pm3.2
    e11
    in1
    eximi
    eximi
    @7
    @13
    vx
    @6
    @12
    vy
    @6
    @12
    @6
    @4
    wps
    @12
    @17
    @6
    @5
    wps
    @18
    wph
    wps
    simpr
    e1a
    @4
    wps
    pm3.2
    e11
    in1
    eximi
    eximi
    jca
    @15
    wch
    @8
    2uasbanhVD.1
    wch
    @8
    wch
    @5
    vy
    vv
    wsb
    #
    vx
    vu
    wsb
    #
    @20
    @8
    wb
    #
    @8
    wch
    wph
    vy
    vv
    wsb
    #
    vx
    vu
    wsb
    #
    wps
    vy
    vv
    wsb
    #
    vx
    vu
    wsb
    #
    @20
    @23
    @25
    wa
    #
    wb
    #
    @20
    wch
    @11
    @23
    @11
    wb
    #
    @23
    wch
    @15
    @11
    wch
    @15
    wch
    @15
    2uasbanhVD.1
    biimpi
    dfvd1ir
    #
    @11
    @14
    simpl
    e1a
    #
    wch
    @0
    @2
    wceq
    vx
    wal
    wn
    @1
    @3
    wceq
    wo
    #
    @28
    wch
    @4
    vy
    wex
    vx
    wex
    #
    @31
    wch
    @11
    @32
    @30
    @9
    @4
    vx
    vy
    @4
    wph
    simpl
    2eximi
    e1a
    @31
    @32
    vx
    vy
    vv
    vu
    ax6e2ndeq
    biimpri
    e1a
    #
    wph
    vx
    vy
    vv
    vu
    2sb5nd
    e1a
    @28
    @11
    @23
    @23
    @11
    biimpr
    com12
    e11
    wch
    @14
    @25
    @14
    wb
    #
    @25
    wch
    @15
    @14
    @29
    @11
    @14
    simpr
    e1a
    wch
    @31
    @34
    @33
    wps
    vx
    vy
    vv
    vu
    2sb5nd
    e1a
    @34
    @14
    @25
    @25
    @14
    biimpr
    com12
    e11
    @20
    @22
    @24
    wa
    #
    vx
    vu
    wsb
    @26
    @19
    @35
    vx
    vu
    wph
    wps
    vy
    vv
    sban
    sbbii
    @22
    @24
    vx
    vu
    sban
    bitri
    @27
    @25
    @23
    @20
    @20
    @23
    @25
    simplbi2comt
    com13
    e110
    wch
    @31
    @21
    @33
    @5
    vx
    vy
    vv
    vu
    2sb5nd
    e1a
    @21
    @20
    @8
    @20
    @8
    biimp
    com12
    e11
    in1
    sylbir
    impbii
end
