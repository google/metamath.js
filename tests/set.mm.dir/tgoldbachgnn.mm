include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "cn.mm"
include "c2.mm"
include "cv.mm"
include "cdvds.mm"
include "wn.mm"
include "crab.mm"
include "syl6eleq.mm"
include "elrabi.mm"
include "syl.mm"
include "cc0.mm"
include "cdc.mm"
include "c7.mm"
include "cexp.mm"
include "co.mm"
include "1red.mm"
include "cr.mm"
include "cn0.mm"
include "10nn0.mm"
include "nn0rei.mm"
include "2nn0.mm"
include "7nn0.mm"
include "deccl.mm"
include "reexpcl.mm"
include "mp2an.mm"
include "a1i.mm"
include "zred.mm"
include "1re.mm"
include "1lt10.mm"
include "ltleii.mm"
include "expge1.mm"
include "mp3an.mm"
include "letrd.mm"
include "elnnz1.mm"
include "sylanbrc.mm"

theorem tgoldbachgnn
  let wph: wff ph
  let vz: setvar z
  let cN: class N
  let cO: class O
  let cH: class H
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let cK: class K
  assume tgoldbachgtda.o: |- O = { z e. ZZ | -. 2 || z }
  assume tgoldbachgtda.n: |- ( ph -> N e. O )
  assume tgoldbachgtda.0: |- ( ph -> ( ; 1 0 ^ ; 2 7 ) <_ N )

  disjoint N z
  disjoint O z
  disjoint H m
  disjoint H n
  disjoint H x
  disjoint m n
  disjoint m x
  disjoint n x
  disjoint K m
  disjoint K n
  disjoint K x
  disjoint N m
  disjoint N n
  disjoint N x
  disjoint m z
  disjoint n z
  disjoint x z
  disjoint O m
  disjoint O n
  disjoint m ph
  disjoint n ph
  disjoint ph x
  assert |- ( ph -> N e. NN )

  proof
    wph
    cN
    cz
    wcel
    #
    c1
    cN
    cle
    wbr
    cN
    cn
    wcel
    wph
    cN
    c2
    vz
    cv
    cdvds
    wbr
    wn
    #
    vz
    cz
    crab
    #
    wcel
    @0
    wph
    cN
    cO
    @2
    tgoldbachgtda.n
    tgoldbachgtda.o
    syl6eleq
    @1
    vz
    cN
    cz
    elrabi
    syl
    #
    wph
    c1
    c1
    cc0
    cdc
    #
    c2
    c7
    cdc
    #
    cexp
    co
    #
    cN
    wph
    1red
    @6
    cr
    wcel
    #
    wph
    @4
    cr
    wcel
    #
    @5
    cn0
    wcel
    #
    @7
    @4
    10nn0
    nn0rei
    #
    c2
    c7
    2nn0
    7nn0
    deccl
    #
    @4
    @5
    reexpcl
    mp2an
    a1i
    wph
    cN
    @3
    zred
    c1
    @6
    cle
    wbr
    #
    wph
    @8
    @9
    c1
    @4
    cle
    wbr
    @12
    @10
    @11
    c1
    @4
    1re
    @10
    1lt10
    ltleii
    @4
    @5
    expge1
    mp3an
    a1i
    tgoldbachgtda.0
    letrd
    cN
    elnnz1
    sylanbrc
end
