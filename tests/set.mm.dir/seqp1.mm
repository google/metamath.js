include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cseq.mm"
include "cvv.mm"
include "cv.mm"
include "cmpt2.mm"
include "cz.mm"
include "wceq.mm"
include "eluzel2.mm"
include "wi.mm"
include "cc0.mm"
include "cif.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "seqeq1.mm"
include "fveq1d.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "cop.mm"
include "crdg.mm"
include "com.mm"
include "cres.mm"
include "cmpt.mm"
include "0z.mm"
include "elimel.mm"
include "eqid.mm"
include "fvex.mm"
include "seqval.mm"
include "uzrdgsuci.mm"
include "dedth.mm"
include "mpcom.mm"
include "elex.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "ovex.mm"
include "ovmpt2.mm"
include "sylancl.mm"
include "eqtrd.mm"

theorem seqp1
  let c.pl: class .+
  let cF: class F
  let cM: class M
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( N e. ( ZZ>= ` M ) -> ( seq M ( .+ , F ) ` ( N + 1 ) ) = ( ( seq M ( .+ , F ) ` N ) .+ ( F ` ( N + 1 ) ) ) )

  proof
    cN
    cM
    cuz
    cfv
    #
    wcel
    #
    cN
    c1
    caddc
    co
    #
    c.pl
    cF
    cM
    cseq
    #
    cfv
    #
    cN
    cN
    @3
    cfv
    #
    vz
    vw
    cvv
    cvv
    vw
    cv
    #
    vz
    cv
    #
    c1
    caddc
    co
    #
    cF
    cfv
    #
    c.pl
    co
    #
    cmpt2
    #
    co
    #
    @5
    @2
    cF
    cfv
    #
    c.pl
    co
    #
    cM
    cz
    wcel
    #
    @1
    @4
    @12
    wceq
    #
    cM
    cN
    eluzel2
    @15
    @1
    @16
    wi
    cN
    @15
    cM
    cc0
    cif
    #
    cuz
    cfv
    #
    wcel
    #
    @2
    c.pl
    cF
    @17
    cseq
    #
    cfv
    #
    cN
    cN
    @20
    cfv
    #
    @11
    co
    #
    wceq
    #
    wi
    cM
    cc0
    cM
    @17
    wceq
    #
    @1
    @19
    @16
    @24
    @25
    @0
    @18
    cN
    cM
    @17
    cuz
    fveq2
    eleq2d
    @25
    @4
    @21
    @12
    @23
    @25
    @2
    @3
    @20
    c.pl
    cF
    cM
    @17
    seqeq1
    #
    fveq1d
    @25
    @5
    @22
    cN
    @11
    @25
    cN
    @3
    @20
    @26
    fveq1d
    oveq2d
    eqeq12d
    imbi12d
    vx
    vy
    @17
    cF
    cfv
    #
    cN
    @17
    vx
    vy
    cvv
    cvv
    vx
    cv
    #
    c1
    caddc
    co
    #
    @28
    vy
    cv
    @11
    co
    cop
    cmpt2
    @17
    @27
    cop
    crdg
    com
    cres
    #
    @20
    @11
    vx
    cvv
    @29
    cmpt
    @17
    crdg
    com
    cres
    #
    cM
    cc0
    cz
    0z
    elimel
    @31
    eqid
    @17
    cF
    fvex
    @30
    eqid
    #
    vx
    vy
    vz
    vw
    c.pl
    @30
    cF
    @17
    @32
    seqval
    uzrdgsuci
    dedth
    mpcom
    @1
    cN
    cvv
    wcel
    @5
    cvv
    wcel
    @12
    @14
    wceq
    cN
    @0
    elex
    cN
    @3
    fvex
    vz
    vw
    cN
    @5
    cvv
    cvv
    @10
    @14
    @11
    @6
    @13
    c.pl
    co
    @7
    cN
    wceq
    #
    @9
    @13
    @6
    c.pl
    @33
    @8
    @2
    cF
    @7
    cN
    c1
    caddc
    oveq1
    fveq2d
    oveq2d
    @6
    @5
    @13
    c.pl
    oveq1
    @11
    eqid
    @5
    @13
    c.pl
    ovex
    ovmpt2
    sylancl
    eqtrd
end
