include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "c1.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "cn0.mm"
include "wf.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "wa.mm"
include "wtru.mm"
include "1nn0.mm"
include "0nn0.mm"
include "keepel.mm"
include "a1i.mm"
include "eqid.mm"
include "fmptd.mm"
include "trud.mm"
include "crab.mm"
include "mptpreima.mm"
include "wss.mm"
include "csn.mm"
include "snfi.mm"
include "cab.mm"
include "cin.mm"
include "inss1.mm"
include "dfrab2.mm"
include "df-sn.mm"
include "3sstr4i.mm"
include "ssfi.mm"
include "mp2an.mm"
include "wi.mm"
include "wn.mm"
include "0nnn.mm"
include "iffalse.mm"
include "eleq1d.mm"
include "mtbiri.mm"
include "con4i.mm"
include "ss2rabi.mm"
include "eqeltri.mm"
include "pm3.2i.mm"
include "psrbag.mm"
include "mpbiri.mm"

theorem psrbagsn
  let vx: setvar x
  let cD: class D
  let vf: setvar f
  let cI: class I
  let cK: class K
  let cV: class V
  assume psrbag0.d: |- D = { f e. ( NN0 ^m I ) | ( `' f " NN ) e. Fin }

  disjoint I f
  disjoint I x
  disjoint f x
  disjoint K f
  disjoint K x
  assert |- ( I e. V -> ( x e. I |-> if ( x = K , 1 , 0 ) ) e. D )

  proof
    cI
    cV
    wcel
    vx
    cI
    vx
    cv
    #
    cK
    wceq
    #
    c1
    cc0
    cif
    #
    cmpt
    #
    cD
    wcel
    cI
    cn0
    @3
    wf
    #
    @3
    ccnv
    cn
    cima
    #
    cfn
    wcel
    #
    wa
    @4
    @6
    @4
    wtru
    vx
    cI
    @2
    cn0
    @3
    @2
    cn0
    wcel
    wtru
    @0
    cI
    wcel
    #
    wa
    @1
    c1
    cc0
    cn0
    1nn0
    0nn0
    keepel
    a1i
    @3
    eqid
    #
    fmptd
    trud
    @5
    @2
    cn
    wcel
    #
    vx
    cI
    crab
    #
    cfn
    vx
    cI
    @2
    cn
    @3
    @8
    mptpreima
    @1
    vx
    cI
    crab
    #
    cfn
    wcel
    #
    @10
    @11
    wss
    @10
    cfn
    wcel
    cK
    csn
    #
    cfn
    wcel
    @11
    @13
    wss
    @12
    cK
    snfi
    @1
    vx
    cab
    #
    cI
    cin
    @14
    @11
    @13
    @14
    cI
    inss1
    @1
    vx
    cI
    dfrab2
    vx
    cK
    df-sn
    3sstr4i
    @13
    @11
    ssfi
    mp2an
    @9
    @1
    vx
    cI
    @9
    @1
    wi
    @7
    @1
    @9
    @1
    wn
    #
    @9
    cc0
    cn
    wcel
    0nnn
    @15
    @2
    cc0
    cn
    @1
    c1
    cc0
    iffalse
    eleq1d
    mtbiri
    con4i
    a1i
    ss2rabi
    @11
    @10
    ssfi
    mp2an
    eqeltri
    pm3.2i
    cD
    vf
    @3
    cI
    cV
    psrbag0.d
    psrbag
    mpbiri
end
