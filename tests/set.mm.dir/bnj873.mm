include "cv.mm"
include "wfn.mm"
include "w3a.mm"
include "wrex.mm"
include "cab.mm"
include "nfv.mm"
include "nfcv.mm"
include "wsbc.mm"
include "nfsbc1v.mm"
include "nfxfr.mm"
include "nf3an.mm"
include "nfrex.mm"
include "weq.mm"
include "fneq1.mm"
include "sbceq1a.mm"
include "syl6bbr.mm"
include "3anbi123d.mm"
include "rexbidv.mm"
include "cbvab.mm"
include "eqtri.mm"

theorem bnj873
  let wph: wff ph
  let wps: wff ps
  let cB: class B
  let cD: class D
  let vf: setvar f
  let vg: setvar g
  let vn: setvar n
  let bnjwphm: wff ph'
  let bnjwpsm: wff ps'
  assume bnj873.4: |- B = { f | E. n e. D ( f Fn n /\ ph /\ ps ) }
  assume bnj873.7: |- ( ph' <-> [. g / f ]. ph )
  assume bnj873.8: |- ( ps' <-> [. g / f ]. ps )

  disjoint D f
  disjoint D g
  disjoint f g
  disjoint f n
  disjoint g n
  disjoint g ph
  disjoint g ps
  assert |- B = { g | E. n e. D ( g Fn n /\ ph' /\ ps' ) }

  proof
    cB
    vf
    cv
    #
    vn
    cv
    #
    wfn
    #
    wph
    wps
    w3a
    #
    vn
    cD
    wrex
    #
    vf
    cab
    vg
    cv
    #
    @1
    wfn
    #
    bnjwphm
    bnjwpsm
    w3a
    #
    vn
    cD
    wrex
    #
    vg
    cab
    bnj873.4
    @4
    @8
    vf
    vg
    @4
    vg
    nfv
    @7
    vf
    vn
    cD
    vf
    cD
    nfcv
    @6
    bnjwphm
    bnjwpsm
    vf
    @6
    vf
    nfv
    bnjwphm
    wph
    vf
    @5
    wsbc
    #
    vf
    bnj873.7
    wph
    vf
    @5
    nfsbc1v
    nfxfr
    bnjwpsm
    wps
    vf
    @5
    wsbc
    #
    vf
    bnj873.8
    wps
    vf
    @5
    nfsbc1v
    nfxfr
    nf3an
    nfrex
    vf
    vg
    weq
    #
    @3
    @7
    vn
    cD
    @11
    @2
    @6
    wph
    bnjwphm
    wps
    bnjwpsm
    @1
    @0
    @5
    fneq1
    @11
    wph
    @9
    bnjwphm
    wph
    vf
    @5
    sbceq1a
    bnj873.7
    syl6bbr
    @11
    wps
    @10
    bnjwpsm
    wps
    vf
    @5
    sbceq1a
    bnj873.8
    syl6bbr
    3anbi123d
    rexbidv
    cbvab
    eqtri
end
