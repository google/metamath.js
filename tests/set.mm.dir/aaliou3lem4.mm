include "c1.mm"
include "cuz.mm"
include "cfv.mm"
include "cv.mm"
include "csu.mm"
include "cr.mm"
include "cn.mm"
include "nnuz.mm"
include "sumeq1i.mm"
include "eqtri.mm"
include "wcel.mm"
include "crp.mm"
include "1nn.mm"
include "caddc.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "c2.mm"
include "cfa.mm"
include "cneg.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "cle.mm"
include "wbr.mm"
include "cdiv.mm"
include "cmin.mm"
include "cmpt.mm"
include "eqid.mm"
include "aaliou3lem3.mm"
include "simp2d.mm"
include "rpre.mm"
include "mp2b.mm"
include "eqeltri.mm"

theorem aaliou3lem4
  let cF: class F
  let cH: class H
  let cL: class L
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let cA: class A
  assume aaliou3lem.c: |- F = ( a e. NN |-> ( 2 ^ -u ( ! ` a ) ) )
  assume aaliou3lem.d: |- L = sum_ b e. NN ( F ` b )
  assume aaliou3lem.e: |- H = ( c e. NN |-> sum_ b e. ( 1 ... c ) ( F ` b ) )

  disjoint a b
  disjoint a c
  disjoint b c
  disjoint F b
  disjoint F c
  disjoint L c
  disjoint a d
  disjoint a e
  disjoint b d
  disjoint b e
  disjoint c d
  disjoint c e
  disjoint d e
  disjoint F d
  disjoint F e
  disjoint L d
  disjoint L e
  disjoint L f
  disjoint c f
  disjoint d f
  disjoint e f
  disjoint H d
  disjoint H e
  disjoint H f
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint A d
  disjoint A e
  assert |- L e. RR

  proof
    cL
    c1
    cuz
    cfv
    #
    vb
    cv
    cF
    cfv
    #
    vb
    csu
    #
    cr
    cL
    cn
    @1
    vb
    csu
    @2
    aaliou3lem.d
    cn
    @0
    @1
    vb
    nnuz
    sumeq1i
    eqtri
    c1
    cn
    wcel
    #
    @2
    crp
    wcel
    #
    @2
    cr
    wcel
    1nn
    @3
    caddc
    cF
    c1
    cseq
    cli
    cdm
    wcel
    @4
    @2
    c2
    c2
    c1
    cfa
    cfv
    cneg
    cexp
    co
    #
    cmul
    co
    cle
    wbr
    c1
    cF
    vc
    @0
    @5
    c1
    c2
    cdiv
    co
    vc
    cv
    c1
    cmin
    co
    cexp
    co
    cmul
    co
    cmpt
    #
    va
    vb
    vc
    @6
    eqid
    aaliou3lem.c
    aaliou3lem3
    simp2d
    @2
    rpre
    mp2b
    eqeltri
end
