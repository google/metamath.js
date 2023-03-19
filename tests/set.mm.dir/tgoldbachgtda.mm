include "cprime.mm"
include "cin.mm"
include "c3.mm"
include "crepr.mm"
include "cfv.mm"
include "co.mm"
include "chash.mm"
include "cn.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cfn.mm"
include "c0.mm"
include "wne.mm"
include "tgoldbachgnn.mm"
include "nnnn0d.mm"
include "cn0.mm"
include "3nn0.mm"
include "a1i.mm"
include "wss.mm"
include "inss2.mm"
include "prmssnn.mm"
include "sstri.mm"
include "reprfi2.mm"
include "wceq.mm"
include "cv.mm"
include "cvma.mm"
include "cmul.mm"
include "c1.mm"
include "c2.mm"
include "csu.mm"
include "tgoldbachgtde.mm"
include "gt0ne0d.mm"
include "neneqd.mm"
include "wa.mm"
include "simpr.mm"
include "sumeq1d.mm"
include "sum0.mm"
include "syl6eq.mm"
include "mtand.mm"
include "neqned.mm"
include "hashnncl.mm"
include "biimpar.mm"
include "syl2anc.mm"
include "nngt0.mm"
include "syl.mm"

theorem tgoldbachgtda
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let vm: setvar m
  let cH: class H
  let cK: class K
  let cN: class N
  let cO: class O
  let vn: setvar n
  assume tgoldbachgtda.o: |- O = { z e. ZZ | -. 2 || z }
  assume tgoldbachgtda.n: |- ( ph -> N e. O )
  assume tgoldbachgtda.0: |- ( ph -> ( ; 1 0 ^ ; 2 7 ) <_ N )
  assume tgoldbachgtda.h: |- ( ph -> H : NN --> ( 0 [,) +oo ) )
  assume tgoldbachgtda.k: |- ( ph -> K : NN --> ( 0 [,) +oo ) )
  assume tgoldbachgtda.1: |- ( ( ph /\ m e. NN ) -> ( K ` m ) <_ ( 1 . _ 0 _ 7 _ 9 _ 9 _ 5 5 ) )
  assume tgoldbachgtda.2: |- ( ( ph /\ m e. NN ) -> ( H ` m ) <_ ( 1 . _ 4 _ 1 4 ) )
  assume tgoldbachgtda.3: |- ( ph -> ( ( 0 . _ 0 _ 0 _ 0 _ 4 _ 2 _ 2 _ 4 8 ) x. ( N ^ 2 ) ) <_ S. ( 0 (,) 1 ) ( ( ( ( ( Lam oF x. H ) vts N ) ` x ) x. ( ( ( ( Lam oF x. K ) vts N ) ` x ) ^ 2 ) ) x. ( exp ` ( ( _i x. ( 2 x. _pi ) ) x. ( -u N x. x ) ) ) ) _d x )

  disjoint H m
  disjoint H x
  disjoint m x
  disjoint K m
  disjoint K x
  disjoint N m
  disjoint N x
  disjoint N z
  disjoint m z
  disjoint x z
  disjoint O m
  disjoint O z
  disjoint m ph
  disjoint ph x
  disjoint H n
  disjoint m n
  disjoint n x
  disjoint K n
  disjoint N n
  disjoint n z
  disjoint O n
  disjoint n ph
  assert |- ( ph -> 0 < ( # ` ( ( O i^i Prime ) ( repr ` 3 ) N ) ) )

  proof
    wph
    cO
    cprime
    cin
    #
    cN
    c3
    crepr
    cfv
    co
    #
    chash
    cfv
    #
    cn
    wcel
    #
    cc0
    @2
    clt
    wbr
    wph
    @1
    cfn
    wcel
    #
    @1
    c0
    wne
    #
    @3
    wph
    @0
    c3
    cN
    wph
    cN
    wph
    vz
    cN
    cO
    tgoldbachgtda.o
    tgoldbachgtda.n
    tgoldbachgtda.0
    tgoldbachgnn
    nnnn0d
    c3
    cn0
    wcel
    wph
    3nn0
    a1i
    @0
    cn
    wss
    wph
    @0
    cprime
    cn
    cO
    cprime
    inss2
    prmssnn
    sstri
    a1i
    reprfi2
    wph
    @1
    c0
    wph
    @1
    c0
    wceq
    #
    @1
    cc0
    vn
    cv
    #
    cfv
    #
    cvma
    cfv
    @8
    cH
    cfv
    cmul
    co
    c1
    @7
    cfv
    #
    cvma
    cfv
    @9
    cK
    cfv
    cmul
    co
    c2
    @7
    cfv
    #
    cvma
    cfv
    @10
    cK
    cfv
    cmul
    co
    cmul
    co
    cmul
    co
    #
    vn
    csu
    #
    cc0
    wceq
    wph
    @12
    cc0
    wph
    @12
    wph
    vx
    vz
    vm
    vn
    cH
    cK
    cN
    cO
    tgoldbachgtda.o
    tgoldbachgtda.n
    tgoldbachgtda.0
    tgoldbachgtda.h
    tgoldbachgtda.k
    tgoldbachgtda.1
    tgoldbachgtda.2
    tgoldbachgtda.3
    tgoldbachgtde
    gt0ne0d
    neneqd
    wph
    @6
    wa
    #
    @12
    c0
    @11
    vn
    csu
    cc0
    @13
    @1
    c0
    @11
    vn
    wph
    @6
    simpr
    sumeq1d
    @11
    vn
    sum0
    syl6eq
    mtand
    neqned
    @4
    @3
    @5
    @1
    hashnncl
    biimpar
    syl2anc
    @2
    nngt0
    syl
end
