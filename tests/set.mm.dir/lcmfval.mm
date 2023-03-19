include "cz.mm"
include "wss.mm"
include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wral.mm"
include "cn.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "cif.mm"
include "cpw.mm"
include "clcmf.mm"
include "cn0.mm"
include "cmpt.mm"
include "wceq.mm"
include "df-lcmf.mm"
include "a1i.mm"
include "eleq2.mm"
include "raleq.mm"
include "rabbidv.mm"
include "infeq1d.mm"
include "ifbieq2d.mm"
include "adantl.mm"
include "cvv.mm"
include "wb.mm"
include "zex.mm"
include "ssex.mm"
include "elpwg.mm"
include "syl.mm"
include "ibir.mm"
include "adantr.mm"
include "0nn0.mm"
include "wn.mm"
include "wnel.mm"
include "df-nel.mm"
include "ssrab2.mm"
include "nnssnn0.mm"
include "sstri.mm"
include "c1.mm"
include "cuz.mm"
include "cfv.mm"
include "c0.mm"
include "wne.mm"
include "nnuz.mm"
include "sseqtri.mm"
include "fissn0dvdsn0.mm"
include "3expa.mm"
include "infssuzcl.mm"
include "sylancr.mm"
include "sseldi.mm"
include "sylan2br.mm"
include "ifclda.mm"
include "fvmptd.mm"

theorem lcmfval
  let vm: setvar m
  let vn: setvar n
  let cZ: class Z
  let vz: setvar z

  disjoint Z m
  disjoint Z n
  disjoint m n
  disjoint Z z
  disjoint m z
  disjoint n z
  assert |- ( ( Z C_ ZZ /\ Z e. Fin ) -> ( _lcm ` Z ) = if ( 0 e. Z , 0 , inf ( { n e. NN | A. m e. Z m || n } , RR , < ) ) )

  proof
    cZ
    cz
    wss
    #
    cZ
    cfn
    wcel
    #
    wa
    #
    vz
    cZ
    cc0
    vz
    cv
    #
    wcel
    #
    cc0
    vm
    cv
    vn
    cv
    cdvds
    wbr
    #
    vm
    @3
    wral
    #
    vn
    cn
    crab
    #
    cr
    clt
    cinf
    #
    cif
    #
    cc0
    cZ
    wcel
    #
    cc0
    @5
    vm
    cZ
    wral
    #
    vn
    cn
    crab
    #
    cr
    clt
    cinf
    #
    cif
    #
    cz
    cpw
    #
    clcmf
    cn0
    clcmf
    vz
    @15
    @9
    cmpt
    wceq
    @2
    vz
    vm
    vn
    df-lcmf
    a1i
    @3
    cZ
    wceq
    #
    @9
    @14
    wceq
    @2
    @16
    @4
    @10
    @8
    @13
    cc0
    @3
    cZ
    cc0
    eleq2
    @16
    cr
    @7
    @12
    clt
    @16
    @6
    @11
    vn
    cn
    @5
    vm
    @3
    cZ
    raleq
    rabbidv
    infeq1d
    ifbieq2d
    adantl
    @0
    cZ
    @15
    wcel
    #
    @1
    @0
    @17
    @0
    cZ
    cvv
    wcel
    @17
    @0
    wb
    cZ
    cz
    zex
    ssex
    cZ
    cz
    cvv
    elpwg
    syl
    ibir
    adantr
    @2
    @10
    cc0
    @13
    cn0
    cc0
    cn0
    wcel
    @2
    @10
    wa
    0nn0
    a1i
    @10
    wn
    @2
    cc0
    cZ
    wnel
    #
    @13
    cn0
    wcel
    cc0
    cZ
    df-nel
    @2
    @18
    wa
    #
    @12
    cn0
    @13
    @12
    cn
    cn0
    @11
    vn
    cn
    ssrab2
    #
    nnssnn0
    sstri
    @19
    @12
    c1
    cuz
    cfv
    #
    wss
    @12
    c0
    wne
    #
    @13
    @12
    wcel
    @12
    cn
    @21
    @20
    nnuz
    sseqtri
    @0
    @1
    @18
    @22
    vm
    vn
    cZ
    fissn0dvdsn0
    3expa
    @12
    c1
    infssuzcl
    sylancr
    sseldi
    sylan2br
    ifclda
    fvmptd
end
