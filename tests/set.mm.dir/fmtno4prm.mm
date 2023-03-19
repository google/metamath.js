include "c4.mm"
include "cfmtno.mm"
include "cfv.mm"
include "cprime.mm"
include "wcel.mm"
include "c2.mm"
include "cuz.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "csqrt.mm"
include "cfl.mm"
include "cfz.mm"
include "co.mm"
include "cin.mm"
include "wral.mm"
include "cexp.mm"
include "c1.mm"
include "caddc.mm"
include "cn0.mm"
include "wceq.mm"
include "4nn0.mm"
include "fmtno.mm"
include "ax-mp.mm"
include "cn.mm"
include "clt.mm"
include "2nn.mm"
include "2nn0.mm"
include "nn0expcli.mm"
include "nnexpcl.mm"
include "mp2an.mm"
include "cr.mm"
include "2re.mm"
include "1lt2.mm"
include "expgt1.mm"
include "mp3an.mm"
include "eluz2b2.mm"
include "mpbir2an.mm"
include "peano2uz.mm"
include "eqeltri.mm"
include "wa.mm"
include "c9.mm"
include "cdc.mm"
include "c3.mm"
include "cle.mm"
include "elinel2.mm"
include "adantr.mm"
include "simpr.mm"
include "elinel1.mm"
include "elfzle2.mm"
include "syl.mm"
include "fmtno4prmfac193.mm"
include "syl3anc.mm"
include "fmtno4nprmfac193.mm"
include "breq1.mm"
include "mtbiri.mm"
include "pm2.01da.mm"
include "rgen.mm"
include "isprm7.mm"

theorem fmtno4prm
  let vk: setvar k
  let vx: setvar x
  let vp: setvar p


  assert |- ( FermatNo ` 4 ) e. Prime

  proof
    c4
    cfmtno
    cfv
    #
    cprime
    wcel
    @0
    c2
    cuz
    cfv
    #
    wcel
    vp
    cv
    #
    @0
    cdvds
    wbr
    #
    wn
    #
    vp
    c2
    @0
    csqrt
    cfv
    cfl
    cfv
    #
    cfz
    co
    #
    cprime
    cin
    #
    wral
    @0
    c2
    c2
    c4
    cexp
    co
    #
    cexp
    co
    #
    c1
    caddc
    co
    #
    @1
    c4
    cn0
    wcel
    #
    @0
    @10
    wceq
    4nn0
    c4
    fmtno
    ax-mp
    @9
    @1
    wcel
    #
    @10
    @1
    wcel
    @12
    @9
    cn
    wcel
    #
    c1
    @9
    clt
    wbr
    #
    c2
    cn
    wcel
    #
    @8
    cn0
    wcel
    @13
    2nn
    c2
    c4
    2nn0
    4nn0
    nn0expcli
    c2
    @8
    nnexpcl
    mp2an
    c2
    cr
    wcel
    @8
    cn
    wcel
    #
    c1
    c2
    clt
    wbr
    @14
    2re
    @15
    @11
    @16
    2nn
    4nn0
    c2
    c4
    nnexpcl
    mp2an
    1lt2
    c2
    @8
    expgt1
    mp3an
    @9
    eluz2b2
    mpbir2an
    c2
    @9
    peano2uz
    ax-mp
    eqeltri
    @4
    vp
    @7
    @2
    @7
    wcel
    #
    @3
    @17
    @3
    wa
    #
    @2
    c1
    c9
    cdc
    c3
    cdc
    #
    wceq
    #
    @4
    @18
    @2
    cprime
    wcel
    #
    @3
    @2
    @5
    cle
    wbr
    #
    @20
    @17
    @21
    @3
    @2
    @6
    cprime
    elinel2
    adantr
    @17
    @3
    simpr
    @17
    @22
    @3
    @17
    @2
    @6
    wcel
    @22
    @2
    @6
    cprime
    elinel1
    @2
    c2
    @5
    elfzle2
    syl
    adantr
    @2
    fmtno4prmfac193
    syl3anc
    @20
    @3
    @19
    @0
    cdvds
    wbr
    fmtno4nprmfac193
    @2
    @19
    @0
    cdvds
    breq1
    mtbiri
    syl
    pm2.01da
    rgen
    vp
    @0
    isprm7
    mpbir2an
end
