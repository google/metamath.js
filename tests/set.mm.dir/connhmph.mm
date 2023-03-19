include "chmph.mm"
include "wbr.mm"
include "chmeo.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "cconn.mm"
include "wcel.mm"
include "wi.mm"
include "hmph.mm"
include "cv.mm"
include "wex.mm"
include "n0.mm"
include "cuni.mm"
include "wfo.mm"
include "ccn.mm"
include "wf1o.mm"
include "eqid.mm"
include "hmeof1o.mm"
include "f1ofo.mm"
include "syl.mm"
include "hmeocn.mm"
include "wa.mm"
include "cnconn.mm"
include "3expb.mm"
include "expcom.mm"
include "syl2anc.mm"
include "exlimiv.mm"
include "sylbi.mm"

theorem connhmph
  let cJ: class J
  let cK: class K
  let vf: setvar f
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( J ~= K -> ( J e. Conn -> K e. Conn ) )

  proof
    cJ
    cK
    chmph
    wbr
    cJ
    cK
    chmeo
    co
    #
    c0
    wne
    #
    cJ
    cconn
    wcel
    #
    cK
    cconn
    wcel
    #
    wi
    #
    cJ
    cK
    hmph
    @1
    vf
    cv
    #
    @0
    wcel
    #
    vf
    wex
    @4
    vf
    @0
    n0
    @6
    @4
    vf
    @6
    cJ
    cuni
    #
    cK
    cuni
    #
    @5
    wfo
    #
    @5
    cJ
    cK
    ccn
    co
    wcel
    #
    @4
    @6
    @7
    @8
    @5
    wf1o
    @9
    @5
    cJ
    cK
    @7
    @8
    @7
    eqid
    @8
    eqid
    #
    hmeof1o
    @7
    @8
    @5
    f1ofo
    syl
    @5
    cJ
    cK
    hmeocn
    @2
    @9
    @10
    wa
    @3
    @2
    @9
    @10
    @3
    @5
    cJ
    cK
    @7
    @8
    @11
    cnconn
    3expb
    expcom
    syl2anc
    exlimiv
    sylbi
    sylbi
end
