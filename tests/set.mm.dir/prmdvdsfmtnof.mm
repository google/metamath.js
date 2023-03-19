include "cfmtno.mm"
include "crn.mm"
include "cprime.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "cn0.mm"
include "wrex.mm"
include "fmtnorn.mm"
include "wa.mm"
include "wor.mm"
include "cfn.mm"
include "c0.mm"
include "wne.mm"
include "wss.mm"
include "ltso.mm"
include "a1i.mm"
include "c2.mm"
include "cuz.mm"
include "cn.mm"
include "c3.mm"
include "fmtnoge3.mm"
include "adantr.mm"
include "wb.mm"
include "eleq1.mm"
include "adantl.mm"
include "mpbid.mm"
include "uzuzle23.mm"
include "syl.mm"
include "eluz2nn.mm"
include "prmdvdsfi.mm"
include "3syl.mm"
include "exprmfct.mm"
include "rabn0.mm"
include "sylibr.mm"
include "ssrab2.mm"
include "prmssnn.mm"
include "nnssre.mm"
include "sstri.mm"
include "w3a.mm"
include "fiinfcl.mm"
include "sseldi.mm"
include "syl13anc.mm"
include "rexlimiva.mm"
include "sylbi.mm"
include "fmpti.mm"

theorem prmdvdsfmtnof
  let vf: setvar f
  let cF: class F
  let vp: setvar p
  let vg: setvar g
  let vh: setvar h
  let vn: setvar n
  let vk: setvar k
  let vx: setvar x
  assume prmdvdsfmtnof.1: |- F = ( f e. ran FermatNo |-> inf ( { p e. Prime | p || f } , RR , < ) )

  disjoint f p
  disjoint F g
  disjoint F h
  disjoint g h
  disjoint f g
  disjoint f h
  disjoint f n
  disjoint g n
  disjoint g p
  disjoint h n
  disjoint h p
  disjoint n p
  disjoint k x
  assert |- F : ran FermatNo --> Prime

  proof
    vf
    cfmtno
    crn
    #
    cprime
    vp
    cv
    vf
    cv
    #
    cdvds
    wbr
    #
    vp
    cprime
    crab
    #
    cr
    clt
    cinf
    #
    cF
    prmdvdsfmtnof.1
    @1
    @0
    wcel
    vn
    cv
    #
    cfmtno
    cfv
    #
    @1
    wceq
    #
    vn
    cn0
    wrex
    @4
    cprime
    wcel
    #
    vn
    @1
    fmtnorn
    @7
    @8
    vn
    cn0
    @5
    cn0
    wcel
    #
    @7
    wa
    #
    cr
    clt
    wor
    #
    @3
    cfn
    wcel
    #
    @3
    c0
    wne
    #
    @3
    cr
    wss
    #
    @8
    @11
    @10
    ltso
    a1i
    @10
    @1
    c2
    cuz
    cfv
    #
    wcel
    #
    @1
    cn
    wcel
    @12
    @10
    @1
    c3
    cuz
    cfv
    #
    wcel
    #
    @16
    @10
    @6
    @17
    wcel
    #
    @18
    @9
    @19
    @7
    @5
    fmtnoge3
    #
    adantr
    @7
    @19
    @18
    wb
    @9
    @6
    @1
    @17
    eleq1
    adantl
    mpbid
    @1
    uzuzle23
    syl
    @1
    eluz2nn
    @1
    vp
    prmdvdsfi
    3syl
    @10
    @2
    vp
    cprime
    wrex
    #
    @13
    @10
    @16
    @21
    @10
    @6
    @15
    wcel
    #
    @16
    @9
    @22
    @7
    @9
    @19
    @22
    @20
    @6
    uzuzle23
    syl
    adantr
    @7
    @22
    @16
    wb
    @9
    @6
    @1
    @15
    eleq1
    adantl
    mpbid
    @1
    vp
    exprmfct
    syl
    @2
    vp
    cprime
    rabn0
    sylibr
    @14
    @10
    @3
    cprime
    cr
    @2
    vp
    cprime
    ssrab2
    #
    cprime
    cn
    cr
    prmssnn
    nnssre
    sstri
    sstri
    a1i
    @11
    @12
    @13
    @14
    w3a
    wa
    @3
    cprime
    @4
    @23
    cr
    @3
    clt
    fiinfcl
    sseldi
    syl13anc
    rexlimiva
    sylbi
    fmpti
end
