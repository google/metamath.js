include "cvv.mm"
include "wcel.mm"
include "clsm.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "ctpos.mm"
include "cbs.mm"
include "cpw.mm"
include "cv.mm"
include "cplusg.mm"
include "cmpt2.mm"
include "crn.mm"
include "eqid.mm"
include "lsmfval.mm"
include "tposeqd.mm"
include "wa.mm"
include "cdm.mm"
include "ccnv.mm"
include "wfo.mm"
include "wrel.mm"
include "reldmmpt2.mm"
include "wfun.mm"
include "mpt2fun.mm"
include "funforn.mm"
include "mpbi.mm"
include "tposfo2.mm"
include "mp2.mm"
include "forn.mm"
include "ax-mp.mm"
include "oppgplus.mm"
include "eqcomi.mm"
include "a1i.mm"
include "mpt2eq3ia.mm"
include "tposmpt2.mm"
include "rneqi.mm"
include "eqtr3i.mm"
include "syl6eq.mm"
include "coppg.mm"
include "fvex.mm"
include "eqeltri.mm"
include "oppgbas.mm"
include "syl6reqr.mm"
include "oveqd.mm"
include "ovtpos.mm"
include "wn.mm"
include "c0.mm"
include "wss.mm"
include "0ex.mm"
include "eqidd.mm"
include "elovmpt2.mm"
include "simp3bi.mm"
include "ssriv.mm"
include "ss0.mm"
include "w3a.mm"
include "elpwi.mm"
include "3ad2ant2.mm"
include "fvprc.mm"
include "3ad2ant1.mm"
include "sseqtrd.mm"
include "syl.mm"
include "mpt2eq12.mm"
include "sylancl.mm"
include "mpt20.mm"
include "rneqd.mm"
include "rn0.mm"
include "mpt2eq3dva.mm"
include "syl5eq.mm"
include "0ov.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"

theorem oppglsm
  let c.po: class .(+)
  let cT: class T
  let cU: class U
  let cG: class G
  let cO: class O
  let vt: setvar t
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  assume oppglsm.o: |- O = ( oppG ` G )
  assume oppglsm.p: |- .(+) = ( LSSum ` G )


  assert |- ( T ( LSSum ` O ) U ) = ( U .(+) T )

  proof
    cG
    cvv
    wcel
    #
    cT
    cU
    cO
    clsm
    cfv
    #
    co
    #
    cU
    cT
    c.po
    co
    #
    wceq
    @0
    @2
    cT
    cU
    c.po
    ctpos
    #
    co
    @3
    @0
    @1
    @4
    cT
    cU
    @0
    @4
    vt
    vu
    cG
    cbs
    cfv
    #
    cpw
    #
    @6
    vx
    vy
    vt
    cv
    #
    vu
    cv
    #
    vx
    cv
    #
    vy
    cv
    #
    cO
    cplusg
    cfv
    #
    co
    #
    cmpt2
    #
    crn
    #
    cmpt2
    #
    @1
    @0
    @4
    vu
    vt
    @6
    @6
    vy
    vx
    @8
    @7
    @10
    @9
    cG
    cplusg
    cfv
    #
    co
    #
    cmpt2
    #
    crn
    #
    cmpt2
    #
    ctpos
    @15
    @0
    c.po
    @20
    vy
    vx
    vt
    vu
    @5
    @16
    c.po
    cG
    cvv
    @5
    eqid
    #
    @16
    eqid
    #
    oppglsm.p
    lsmfval
    tposeqd
    vu
    vt
    @6
    @6
    @14
    @20
    vu
    vt
    @6
    @6
    @19
    @14
    @19
    @14
    wceq
    @8
    @6
    wcel
    #
    @7
    @6
    wcel
    #
    wa
    @18
    ctpos
    #
    crn
    #
    @19
    @14
    @18
    cdm
    #
    ccnv
    #
    @19
    @25
    wfo
    #
    @26
    @19
    wceq
    @27
    wrel
    @27
    @19
    @18
    wfo
    #
    @29
    vy
    vx
    @8
    @7
    @17
    @18
    @18
    eqid
    #
    reldmmpt2
    @18
    wfun
    @30
    vy
    vx
    @8
    @7
    @17
    @18
    @31
    mpt2fun
    @18
    funforn
    mpbi
    @27
    @19
    @18
    tposfo2
    mp2
    @28
    @19
    @25
    forn
    ax-mp
    @25
    @13
    vy
    vx
    @8
    @7
    @12
    @18
    vy
    vx
    @8
    @7
    @17
    @12
    @17
    @12
    wceq
    @10
    @8
    wcel
    @9
    @7
    wcel
    wa
    @12
    @17
    @16
    @11
    cG
    cO
    @9
    @10
    @22
    oppglsm.o
    @11
    eqid
    #
    oppgplus
    eqcomi
    a1i
    mpt2eq3ia
    tposmpt2
    rneqi
    eqtr3i
    a1i
    mpt2eq3ia
    tposmpt2
    syl6eq
    cO
    cvv
    wcel
    @1
    @15
    wceq
    cO
    cG
    coppg
    cfv
    cvv
    oppglsm.o
    cG
    coppg
    fvex
    eqeltri
    vx
    vy
    vu
    vt
    @5
    @11
    @1
    cO
    cvv
    @5
    cG
    cO
    oppglsm.o
    @21
    oppgbas
    @32
    @1
    eqid
    lsmfval
    ax-mp
    #
    syl6reqr
    oveqd
    cT
    cU
    c.po
    ovtpos
    syl6eq
    @0
    wn
    #
    cT
    cU
    vt
    vu
    @6
    @6
    c0
    cmpt2
    #
    co
    #
    c0
    @2
    @3
    @36
    c0
    wss
    @36
    c0
    wceq
    vx
    @36
    c0
    @9
    @36
    wcel
    cT
    @6
    wcel
    cU
    @6
    wcel
    @9
    c0
    wcel
    @6
    @6
    c0
    @35
    c0
    @9
    cT
    cU
    vt
    vu
    @35
    eqid
    0ex
    @7
    cT
    wceq
    @8
    cU
    wceq
    wa
    c0
    eqidd
    elovmpt2
    simp3bi
    ssriv
    @36
    ss0
    ax-mp
    @34
    @1
    @35
    cT
    cU
    @34
    @1
    @15
    @35
    @33
    @34
    vt
    vu
    @6
    @6
    @14
    c0
    @34
    @24
    @23
    w3a
    #
    @14
    c0
    crn
    c0
    @37
    @13
    c0
    @37
    @13
    vx
    vy
    c0
    @8
    @12
    cmpt2
    #
    c0
    @37
    @7
    c0
    wceq
    #
    @8
    @8
    wceq
    @13
    @38
    wceq
    @37
    @7
    c0
    wss
    @39
    @37
    @7
    @5
    c0
    @24
    @34
    @7
    @5
    wss
    @23
    @7
    @5
    elpwi
    3ad2ant2
    @34
    @24
    @5
    c0
    wceq
    @23
    cG
    cbs
    fvprc
    3ad2ant1
    sseqtrd
    @7
    ss0
    syl
    @8
    eqid
    vx
    vy
    @7
    @8
    c0
    @8
    @12
    mpt2eq12
    sylancl
    vx
    vy
    @8
    @12
    mpt20
    syl6eq
    rneqd
    rn0
    syl6eq
    mpt2eq3dva
    syl5eq
    oveqd
    @34
    @3
    cU
    cT
    c0
    co
    c0
    @34
    c.po
    c0
    cU
    cT
    @34
    c.po
    cG
    clsm
    cfv
    c0
    oppglsm.p
    cG
    clsm
    fvprc
    syl5eq
    oveqd
    cU
    cT
    0ov
    syl6eq
    3eqtr4a
    pm2.61i
end
