include "cz.mm"
include "wcel.mm"
include "cseq.mm"
include "cuz.mm"
include "cfv.mm"
include "wfn.mm"
include "cc0.mm"
include "cif.mm"
include "wceq.mm"
include "seqeq1.mm"
include "fveq2.mm"
include "fneq12d.mm"
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
include "uzrdgfni.mm"
include "dedth.mm"

theorem seqfn
  let c.pl: class .+
  let cF: class F
  let cM: class M
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( M e. ZZ -> seq M ( .+ , F ) Fn ( ZZ>= ` M ) )

  proof
    cM
    cz
    wcel
    #
    c.pl
    cF
    cM
    cseq
    #
    cM
    cuz
    cfv
    #
    wfn
    c.pl
    cF
    @0
    cM
    cc0
    cif
    #
    cseq
    #
    @3
    cuz
    cfv
    #
    wfn
    cM
    cc0
    cM
    @3
    wceq
    @2
    @5
    @1
    @4
    c.pl
    cF
    cM
    @3
    seqeq1
    cM
    @3
    cuz
    fveq2
    fneq12d
    vx
    vy
    @3
    cF
    cfv
    #
    @3
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
    @7
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
    @3
    @6
    cop
    crdg
    com
    cres
    #
    @4
    @9
    vx
    cvv
    @8
    cmpt
    @3
    crdg
    com
    cres
    #
    cM
    cc0
    cz
    0z
    elimel
    @11
    eqid
    @3
    cF
    fvex
    @10
    eqid
    #
    vx
    vy
    vz
    vw
    c.pl
    @10
    cF
    @3
    @12
    seqval
    uzrdgfni
    dedth
end
