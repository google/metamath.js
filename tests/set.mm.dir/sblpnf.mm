include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "cpnf.mm"
include "cbl.mm"
include "co.mm"
include "wceq.mm"
include "cr.mm"
include "cc.mm"
include "cpr.mm"
include "wo.mm"
include "elpri.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cxp.mm"
include "cres.mm"
include "eqid.mm"
include "remet.mm"
include "xpeq12.mm"
include "anidms.mm"
include "reseq2d.mm"
include "fveq2.mm"
include "eleq12d.mm"
include "mpbiri.mm"
include "syl5eqel.mm"
include "cdm.mm"
include "wrel.mm"
include "relco.mm"
include "resdm.mm"
include "ax-mp.mm"
include "wf.mm"
include "wss.mm"
include "absf.mm"
include "ax-resscn.mm"
include "fss.mm"
include "mp2an.mm"
include "subf.mm"
include "fco.mm"
include "fdmi.mm"
include "reseq2i.mm"
include "eqtr3i.mm"
include "cnmet.mm"
include "eqeltrri.mm"
include "jaoi.mm"
include "3syl.mm"
include "blpnf.mm"
include "sylan.mm"

theorem sblpnf
  let wph: wff ph
  let cD: class D
  let cP: class P
  let cS: class S
  assume sblpnf.s: |- ( ph -> S e. { RR , CC } )
  assume sblpnf.d: |- D = ( ( abs o. - ) |` ( S X. S ) )


  assert |- ( ( ph /\ P e. S ) -> ( P ( ball ` D ) +oo ) = S )

  proof
    wph
    cD
    cS
    cme
    cfv
    #
    wcel
    #
    cP
    cS
    wcel
    cP
    cpnf
    cD
    cbl
    cfv
    co
    cS
    wceq
    wph
    cS
    cr
    cc
    cpr
    wcel
    cS
    cr
    wceq
    #
    cS
    cc
    wceq
    #
    wo
    @1
    sblpnf.s
    cS
    cr
    cc
    elpri
    @2
    @1
    @3
    @2
    cD
    cabs
    cmin
    ccom
    #
    cS
    cS
    cxp
    #
    cres
    #
    @0
    sblpnf.d
    @2
    @6
    @0
    wcel
    #
    @4
    cr
    cr
    cxp
    #
    cres
    #
    cr
    cme
    cfv
    #
    wcel
    @9
    @9
    eqid
    remet
    @2
    @6
    @9
    @0
    @10
    @2
    @5
    @8
    @4
    @2
    @5
    @8
    wceq
    cS
    cr
    cS
    cr
    xpeq12
    anidms
    reseq2d
    cS
    cr
    cme
    fveq2
    eleq12d
    mpbiri
    syl5eqel
    @3
    cD
    @6
    @0
    sblpnf.d
    @3
    @7
    @4
    cc
    cc
    cxp
    #
    cres
    #
    cc
    cme
    cfv
    #
    wcel
    @4
    @12
    @13
    @4
    @4
    cdm
    #
    cres
    #
    @4
    @12
    @4
    wrel
    @15
    @4
    wceq
    cabs
    cmin
    relco
    @4
    resdm
    ax-mp
    @14
    @11
    @4
    @11
    cc
    @4
    cc
    cc
    cabs
    wf
    #
    @11
    cc
    cmin
    wf
    @11
    cc
    @4
    wf
    cc
    cr
    cabs
    wf
    cr
    cc
    wss
    @16
    absf
    ax-resscn
    cc
    cr
    cc
    cabs
    fss
    mp2an
    subf
    @11
    cc
    cc
    cabs
    cmin
    fco
    mp2an
    fdmi
    reseq2i
    eqtr3i
    cnmet
    eqeltrri
    @3
    @6
    @12
    @0
    @13
    @3
    @5
    @11
    @4
    @3
    @5
    @11
    wceq
    cS
    cc
    cS
    cc
    xpeq12
    anidms
    reseq2d
    cS
    cc
    cme
    fveq2
    eleq12d
    mpbiri
    syl5eqel
    jaoi
    3syl
    cD
    cP
    cS
    blpnf
    sylan
end
