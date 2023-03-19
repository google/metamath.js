include "crg.mm"
include "cnzr.mm"
include "cdif.mm"
include "wcel.mm"
include "wa.mm"
include "c0g.mm"
include "cfv.mm"
include "cv.mm"
include "cur.mm"
include "wceq.mm"
include "crh.mm"
include "co.mm"
include "wral.mm"
include "c0.mm"
include "cbs.mm"
include "eqid.mm"
include "0ring1eq0.mm"
include "adantr.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "rhm1.mm"
include "adantl.mm"
include "eqtrd.mm"
include "cghm.mm"
include "rhmghm.mm"
include "ghmid.mm"
include "syl.mm"
include "jca.mm"
include "ralrimiva.mm"
include "wi.mm"
include "wal.mm"
include "wn.mm"
include "wne.mm"
include "wo.mm"
include "nzrnz.mm"
include "necomd.mm"
include "wb.mm"
include "neeq1.mm"
include "mpbird.mm"
include "orcd.mm"
include "expcom.mm"
include "olc.mm"
include "a1d.mm"
include "pm2.61ine.mm"
include "neorian.mm"
include "sylib.mm"
include "con3.mm"
include "syl5com.mm"
include "alimdv.mm"
include "df-ral.mm"
include "eq0.mm"
include "3imtr4g.mm"
include "mpd.mm"

theorem nrhmzr
  let cR: class R
  let cZ: class Z
  let vf: setvar f
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( Z e. ( Ring \ NzRing ) /\ R e. NzRing ) -> ( Z RingHom R ) = (/) )

  proof
    cZ
    crg
    cnzr
    cdif
    wcel
    #
    cR
    cnzr
    wcel
    #
    wa
    #
    cZ
    c0g
    cfv
    #
    vf
    cv
    #
    cfv
    #
    cR
    cur
    cfv
    #
    wceq
    #
    @5
    cR
    c0g
    cfv
    #
    wceq
    #
    wa
    #
    vf
    cZ
    cR
    crh
    co
    #
    wral
    #
    @11
    c0
    wceq
    #
    @2
    @10
    vf
    @11
    @2
    @4
    @11
    wcel
    #
    wa
    #
    @7
    @9
    @15
    @5
    cZ
    cur
    cfv
    #
    @4
    cfv
    #
    @6
    @15
    @3
    @16
    @4
    @15
    @16
    @3
    @2
    @16
    @3
    wceq
    #
    @14
    @0
    @18
    @1
    cZ
    cbs
    cfv
    #
    cZ
    @16
    @3
    @19
    eqid
    @3
    eqid
    #
    @16
    eqid
    #
    0ring1eq0
    adantr
    adantr
    eqcomd
    fveq2d
    @14
    @17
    @6
    wceq
    @2
    cZ
    cR
    @16
    @4
    @6
    @21
    @6
    eqid
    #
    rhm1
    adantl
    eqtrd
    @15
    @4
    cZ
    cR
    cghm
    co
    wcel
    #
    @9
    @14
    @23
    @2
    cZ
    cR
    @4
    rhmghm
    adantl
    cZ
    cR
    @4
    @3
    @8
    @20
    @8
    eqid
    #
    ghmid
    syl
    jca
    ralrimiva
    @2
    @14
    @10
    wi
    #
    vf
    wal
    @14
    wn
    #
    vf
    wal
    @12
    @13
    @2
    @25
    @26
    vf
    @2
    @10
    wn
    #
    @25
    @26
    @2
    @5
    @6
    wne
    #
    @5
    @8
    wne
    #
    wo
    #
    @27
    @2
    @30
    wi
    @5
    @8
    @2
    @9
    @30
    @2
    @9
    wa
    #
    @28
    @29
    @31
    @28
    @8
    @6
    wne
    #
    @2
    @32
    @9
    @1
    @32
    @0
    @1
    @6
    @8
    cR
    @6
    @8
    @22
    @24
    nzrnz
    necomd
    adantl
    adantr
    @9
    @28
    @32
    wb
    @2
    @5
    @8
    @6
    neeq1
    adantl
    mpbird
    orcd
    expcom
    @29
    @30
    @2
    @29
    @28
    olc
    a1d
    pm2.61ine
    @5
    @6
    @5
    @8
    neorian
    sylib
    @14
    @10
    con3
    syl5com
    alimdv
    @10
    vf
    @11
    df-ral
    vf
    @11
    eq0
    3imtr4g
    mpd
end
