include "com.mm"
include "wf1.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "c2o.mm"
include "comu.mm"
include "co.mm"
include "wcel.mm"
include "2onn.mm"
include "nnmcl.mm"
include "mpan.mm"
include "fmpti.mm"
include "wa.mm"
include "fin1a2lem3.mm"
include "eqeqan12d.mm"
include "con0.mm"
include "c0.mm"
include "wb.mm"
include "2on.mm"
include "a1i.mm"
include "nnon.mm"
include "adantr.mm"
include "adantl.mm"
include "c1o.mm"
include "csuc.mm"
include "0lt1o.mm"
include "elelsuc.mm"
include "ax-mp.mm"
include "df-2o.mm"
include "eleqtrri.mm"
include "omcan.mm"
include "syl31anc.mm"
include "bitrd.mm"
include "biimpd.mm"
include "rgen2a.mm"
include "dff13.mm"
include "mpbir2an.mm"

theorem fin1a2lem4
  let vx: setvar x
  let cE: class E
  let va: setvar a
  let vf: setvar f
  let vy: setvar y
  let cA: class A
  let vb: setvar b
  let cS: class S
  assume fin1a2lem.b: |- E = ( x e. _om |-> ( 2o .o x ) )


  assert |- E : _om -1-1-> _om

  proof
    com
    com
    cE
    wf1
    com
    com
    cE
    wf
    va
    cv
    #
    cE
    cfv
    #
    vb
    cv
    #
    cE
    cfv
    #
    wceq
    #
    va
    vb
    weq
    #
    wi
    #
    vb
    com
    wral
    va
    com
    wral
    vx
    com
    com
    c2o
    vx
    cv
    #
    comu
    co
    #
    cE
    fin1a2lem.b
    c2o
    com
    wcel
    @7
    com
    wcel
    @8
    com
    wcel
    2onn
    c2o
    @7
    nnmcl
    mpan
    fmpti
    @6
    va
    vb
    com
    @0
    com
    wcel
    #
    @2
    com
    wcel
    #
    wa
    #
    @4
    @5
    @11
    @4
    c2o
    @0
    comu
    co
    #
    c2o
    @2
    comu
    co
    #
    wceq
    #
    @5
    @9
    @10
    @1
    @12
    @3
    @13
    vx
    @0
    cE
    fin1a2lem.b
    fin1a2lem3
    vx
    @2
    cE
    fin1a2lem.b
    fin1a2lem3
    eqeqan12d
    @11
    c2o
    con0
    wcel
    #
    @0
    con0
    wcel
    #
    @2
    con0
    wcel
    #
    c0
    c2o
    wcel
    #
    @14
    @5
    wb
    @15
    @11
    2on
    a1i
    @9
    @16
    @10
    @0
    nnon
    adantr
    @10
    @17
    @9
    @2
    nnon
    adantl
    @18
    @11
    c0
    c1o
    csuc
    #
    c2o
    c0
    c1o
    wcel
    c0
    @19
    wcel
    0lt1o
    c0
    c1o
    elelsuc
    ax-mp
    df-2o
    eleqtrri
    a1i
    c2o
    @0
    @2
    omcan
    syl31anc
    bitrd
    biimpd
    rgen2a
    va
    vb
    com
    com
    cE
    dff13
    mpbir2an
end
