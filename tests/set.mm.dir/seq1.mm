include "cz.mm"
include "wcel.mm"
include "cseq.mm"
include "cfv.mm"
include "wceq.mm"
include "cc0.mm"
include "cif.mm"
include "seqeq1.mm"
include "id.mm"
include "fveq12d.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "cvv.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cmpt2.mm"
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
include "uzrdg0i.mm"
include "dedth.mm"

theorem seq1
  let c.pl: class .+
  let cF: class F
  let cM: class M
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( M e. ZZ -> ( seq M ( .+ , F ) ` M ) = ( F ` M ) )

  proof
    cM
    cz
    wcel
    #
    cM
    c.pl
    cF
    cM
    cseq
    #
    cfv
    #
    cM
    cF
    cfv
    #
    wceq
    @0
    cM
    cc0
    cif
    #
    c.pl
    cF
    @4
    cseq
    #
    cfv
    #
    @4
    cF
    cfv
    #
    wceq
    cM
    cc0
    cM
    @4
    wceq
    #
    @2
    @6
    @3
    @7
    @8
    cM
    @4
    @1
    @5
    c.pl
    cF
    cM
    @4
    seqeq1
    @8
    id
    fveq12d
    cM
    @4
    cF
    fveq2
    eqeq12d
    vx
    vy
    @7
    @4
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
    @9
    vy
    cv
    vz
    vw
    cvv
    cvv
    vw
    cv
    vz
    cv
    c1
    caddc
    co
    cF
    cfv
    c.pl
    co
    cmpt2
    #
    co
    cop
    cmpt2
    @4
    @7
    cop
    crdg
    com
    cres
    #
    @5
    @11
    vx
    cvv
    @10
    cmpt
    @4
    crdg
    com
    cres
    #
    cM
    cc0
    cz
    0z
    elimel
    @13
    eqid
    @4
    cF
    fvex
    @12
    eqid
    #
    vx
    vy
    vz
    vw
    c.pl
    @12
    cF
    @4
    @14
    seqval
    uzrdg0i
    dedth
end
