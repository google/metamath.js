include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cid.mm"
include "cdif.mm"
include "cdm.mm"
include "csn.mm"
include "cuni.mm"
include "cif.mm"
include "wceq.mm"
include "pmtrdifellem1.mm"
include "cpmtr.mm"
include "eqid.mm"
include "pmtrffv.mm"
include "sylan.mm"
include "wn.mm"
include "csymg.mm"
include "cbs.mm"
include "wf.mm"
include "wi.mm"
include "symgtrf.mm"
include "sseli.mm"
include "symgbasf.mm"
include "wfn.mm"
include "cv.mm"
include "wne.mm"
include "crab.mm"
include "ffn.mm"
include "fndifnfp.mm"
include "wss.mm"
include "ssrab2.mm"
include "ssel2.mm"
include "eldif.mm"
include "elsng.mm"
include "notbid.mm"
include "pm2.24i.mm"
include "syl6bi.mm"
include "imp.mm"
include "sylbi.mm"
include "syl.mm"
include "mpan.mm"
include "con2i.mm"
include "eleq2.mm"
include "syl5ibr.mm"
include "3syl.mm"
include "wb.mm"
include "pmtrdifellem2.mm"
include "eleq2d.mm"
include "adantr.mm"
include "mtbird.mm"
include "iffalsed.mm"
include "eqtrd.mm"

theorem pmtrdifellem4
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cK: class K
  let cN: class N
  let vx: setvar x
  assume pmtrdifel.t: |- T = ran ( pmTrsp ` ( N \ { K } ) )
  assume pmtrdifel.r: |- R = ran ( pmTrsp ` N )
  assume pmtrdifel.0: |- S = ( ( pmTrsp ` N ) ` dom ( Q \ _I ) )


  assert |- ( ( Q e. T /\ K e. N ) -> ( S ` K ) = K )

  proof
    cQ
    cT
    wcel
    #
    cK
    cN
    wcel
    #
    wa
    #
    cK
    cS
    cfv
    #
    cK
    cS
    cid
    cdif
    cdm
    #
    wcel
    #
    @4
    cK
    csn
    #
    cdif
    cuni
    #
    cK
    cif
    #
    cK
    @0
    cS
    cR
    wcel
    @1
    @3
    @8
    wceq
    cQ
    cR
    cS
    cT
    cK
    cN
    pmtrdifel.t
    pmtrdifel.r
    pmtrdifel.0
    pmtrdifellem1
    cN
    @4
    cR
    cN
    cpmtr
    cfv
    #
    cS
    cK
    @9
    eqid
    pmtrdifel.r
    @4
    eqid
    pmtrffv
    sylan
    @2
    @5
    @7
    cK
    @2
    @5
    cK
    cQ
    cid
    cdif
    cdm
    #
    wcel
    #
    @0
    @1
    @11
    wn
    #
    @0
    cQ
    cN
    @6
    cdif
    #
    csymg
    cfv
    #
    cbs
    cfv
    #
    wcel
    @13
    @13
    cQ
    wf
    #
    @1
    @12
    wi
    #
    cT
    @15
    cQ
    @15
    @13
    cT
    @14
    pmtrdifel.t
    @14
    eqid
    #
    @15
    eqid
    #
    symgtrf
    sseli
    @13
    @15
    cQ
    @14
    @18
    @19
    symgbasf
    @16
    cQ
    @13
    wfn
    @10
    vx
    cv
    #
    cQ
    cfv
    @20
    wne
    #
    vx
    @13
    crab
    #
    wceq
    #
    @17
    @13
    @13
    cQ
    ffn
    vx
    @13
    cQ
    fndifnfp
    @1
    @12
    @23
    cK
    @22
    wcel
    #
    wn
    @24
    @1
    @22
    @13
    wss
    #
    @24
    @1
    wn
    #
    @21
    vx
    @13
    ssrab2
    @25
    @24
    wa
    cK
    @13
    wcel
    #
    @26
    @22
    @13
    cK
    ssel2
    @27
    @1
    cK
    @6
    wcel
    #
    wn
    #
    wa
    @26
    cK
    cN
    @6
    eldif
    @1
    @29
    @26
    @1
    @29
    cK
    cK
    wceq
    #
    wn
    @26
    @1
    @28
    @30
    cK
    cK
    cN
    elsng
    notbid
    @30
    @26
    cK
    eqid
    pm2.24i
    syl6bi
    imp
    sylbi
    syl
    mpan
    con2i
    @23
    @11
    @24
    @10
    @22
    cK
    eleq2
    notbid
    syl5ibr
    3syl
    3syl
    imp
    @0
    @5
    @11
    wb
    @1
    @0
    @4
    @10
    cK
    cQ
    cR
    cS
    cT
    cK
    cN
    pmtrdifel.t
    pmtrdifel.r
    pmtrdifel.0
    pmtrdifellem2
    eleq2d
    adantr
    mtbird
    iffalsed
    eqtrd
end
