include "cr.mm"
include "cc.mm"
include "cpr.mm"
include "wcel.mm"
include "wceq.mm"
include "wo.mm"
include "ce.mm"
include "cres.mm"
include "wf.mm"
include "elpri.mm"
include "crp.mm"
include "wf1.mm"
include "reeff1.mm"
include "f1f.mm"
include "wss.mm"
include "rpssre.mm"
include "fss.mm"
include "mpan2.mm"
include "mp2b.mm"
include "wb.mm"
include "feq23.mm"
include "anidms.mm"
include "mpbiri.mm"
include "reseq2.mm"
include "feq1d.mm"
include "mpbird.mm"
include "eff.mm"
include "cdm.mm"
include "wrel.mm"
include "frel.mm"
include "resdm.mm"
include "fdmi.mm"
include "reseq2i.mm"
include "eqtr3i.mm"
include "feq1i.mm"
include "mpbi.mm"
include "jaoi.mm"
include "3syl.mm"

theorem seff
  let wph: wff ph
  let cS: class S
  assume seff.s: |- ( ph -> S e. { RR , CC } )


  assert |- ( ph -> ( exp |` S ) : S --> S )

  proof
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
    cS
    cS
    ce
    cS
    cres
    #
    wf
    #
    seff.s
    cS
    cr
    cc
    elpri
    @0
    @3
    @1
    @0
    @3
    cS
    cS
    ce
    cr
    cres
    #
    wf
    #
    @0
    @5
    cr
    cr
    @4
    wf
    #
    cr
    crp
    @4
    wf1
    cr
    crp
    @4
    wf
    #
    @6
    reeff1
    cr
    crp
    @4
    f1f
    @7
    crp
    cr
    wss
    @6
    rpssre
    cr
    crp
    cr
    @4
    fss
    mpan2
    mp2b
    @0
    @5
    @6
    wb
    cS
    cS
    cr
    cr
    @4
    feq23
    anidms
    mpbiri
    @0
    cS
    cS
    @2
    @4
    cS
    cr
    ce
    reseq2
    feq1d
    mpbird
    @1
    @3
    cS
    cS
    ce
    cc
    cres
    #
    wf
    #
    @1
    @9
    cc
    cc
    @8
    wf
    #
    cc
    cc
    ce
    wf
    #
    @10
    eff
    cc
    cc
    ce
    @8
    ce
    ce
    cdm
    #
    cres
    #
    ce
    @8
    @11
    ce
    wrel
    @13
    ce
    wceq
    eff
    cc
    cc
    ce
    frel
    ce
    resdm
    mp2b
    @12
    cc
    ce
    cc
    cc
    ce
    eff
    fdmi
    reseq2i
    eqtr3i
    feq1i
    mpbi
    @1
    @9
    @10
    wb
    cS
    cS
    cc
    cc
    @8
    feq23
    anidms
    mpbiri
    @1
    cS
    cS
    @2
    @8
    cS
    cc
    ce
    reseq2
    feq1d
    mpbird
    jaoi
    3syl
end
