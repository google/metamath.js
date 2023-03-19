include "cn.mm"
include "cho.mm"
include "wf.mm"
include "ch0o.mm"
include "csn.mm"
include "cxp.mm"
include "c1.mm"
include "cseq.mm"
include "wtru.mm"
include "nnuz.mm"
include "1zzd.mm"
include "cv.mm"
include "wcel.mm"
include "cfv.mm"
include "0hmop.mm"
include "elexi.mm"
include "fvconst2.mm"
include "syl6eqel.mm"
include "adantl.mm"
include "wa.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "ccom.mm"
include "chod.mm"
include "chot.mm"
include "chos.mm"
include "opsqrlem3.mm"
include "cr.mm"
include "halfre.mm"
include "wceq.mm"
include "simpl.mm"
include "eqidd.mm"
include "hmopco.mm"
include "syl3anc.mm"
include "hmopd.mm"
include "sylancr.mm"
include "hmopm.mm"
include "hmops.mm"
include "syldan.mm"
include "eqeltrd.mm"
include "seqf.mm"
include "trud.mm"
include "feq1i.mm"
include "mpbir.mm"

theorem opsqrlem4
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cT: class T
  let cF: class F
  let vj: setvar j
  let vk: setvar k
  let vw: setvar w
  let vz: setvar z
  let cG: class G
  let cN: class N
  let cH: class H
  assume opsqrlem2.1: |- T e. HrmOp
  assume opsqrlem2.2: |- S = ( x e. HrmOp , y e. HrmOp |-> ( x +op ( ( 1 / 2 ) .op ( T -op ( x o. x ) ) ) ) )
  assume opsqrlem2.3: |- F = seq 1 ( S , ( NN X. { 0hop } ) )

  disjoint x y
  disjoint T x
  disjoint T y
  disjoint j k
  disjoint F j
  disjoint F k
  disjoint w z
  disjoint G w
  disjoint G z
  disjoint N j
  disjoint N k
  disjoint S w
  disjoint S z
  disjoint w x
  disjoint w y
  disjoint T w
  disjoint x z
  disjoint y z
  disjoint T z
  disjoint H w
  disjoint H z
  assert |- F : NN --> HrmOp

  proof
    cn
    cho
    cF
    wf
    cn
    cho
    cS
    cn
    ch0o
    csn
    cxp
    #
    c1
    cseq
    #
    wf
    #
    @2
    wtru
    vz
    vw
    cS
    cho
    @0
    c1
    cn
    nnuz
    wtru
    1zzd
    vz
    cv
    #
    cn
    wcel
    #
    @3
    @0
    cfv
    #
    cho
    wcel
    wtru
    @4
    @5
    ch0o
    cho
    cn
    ch0o
    @3
    ch0o
    cho
    0hmop
    elexi
    fvconst2
    0hmop
    syl6eqel
    adantl
    @3
    cho
    wcel
    #
    vw
    cv
    #
    cho
    wcel
    #
    wa
    #
    @3
    @7
    cS
    co
    #
    cho
    wcel
    wtru
    @9
    @10
    @3
    c1
    c2
    cdiv
    co
    #
    cT
    @3
    @3
    ccom
    #
    chod
    co
    #
    chot
    co
    #
    chos
    co
    #
    cho
    vx
    vy
    cS
    cT
    cF
    @3
    @7
    opsqrlem2.1
    opsqrlem2.2
    opsqrlem2.3
    opsqrlem3
    @6
    @8
    @14
    cho
    wcel
    #
    @15
    cho
    wcel
    @9
    @11
    cr
    wcel
    @13
    cho
    wcel
    #
    @16
    halfre
    @9
    cT
    cho
    wcel
    @12
    cho
    wcel
    #
    @17
    opsqrlem2.1
    @9
    @6
    @6
    @12
    @12
    wceq
    @18
    @6
    @8
    simpl
    #
    @19
    @9
    @12
    eqidd
    @3
    @3
    hmopco
    syl3anc
    cT
    @12
    hmopd
    sylancr
    @11
    @13
    hmopm
    sylancr
    @3
    @14
    hmops
    syldan
    eqeltrd
    adantl
    seqf
    trud
    cn
    cho
    cF
    @1
    opsqrlem2.3
    feq1i
    mpbir
end
