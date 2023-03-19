include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "csn.mm"
include "cdif.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cmin.mm"
include "cn.mm"
include "fz1ssnn.mm"
include "sseldi.mm"
include "nnred.mm"
include "1red.mm"
include "resubcld.mm"
include "elfzle2.mm"
include "syl.mm"
include "lem1d.mm"
include "letrd.mm"
include "jca.mm"
include "cz.mm"
include "wb.mm"
include "nnzd.mm"
include "elfz.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "cc0.mm"
include "nnnn0d.mm"
include "nn0ge0d.mm"
include "cr.mm"
include "1re.mm"
include "addge02.mm"
include "sylancr.mm"
include "mpbid.mm"
include "clt.mm"
include "cn0.mm"
include "nn0ltlem1.mm"
include "syl2anc.mm"
include "nnltp1le.mm"
include "peano2zd.mm"
include "1zzd.mm"
include "wne.mm"
include "wn.mm"
include "nnleltp1.mm"
include "ltned.mm"
include "necomd.mm"
include "nelsn.mm"
include "eldifd.mm"

theorem submateqlem1
  let wph: wff ph
  let cK: class K
  let cM: class M
  let cN: class N
  assume submateqlem1.n: |- ( ph -> N e. NN )
  assume submateqlem1.k: |- ( ph -> K e. ( 1 ... N ) )
  assume submateqlem1.m: |- ( ph -> M e. ( 1 ... ( N - 1 ) ) )
  assume submateqlem1.1: |- ( ph -> K <_ M )


  assert |- ( ph -> ( M e. ( K ... N ) /\ ( M + 1 ) e. ( ( 1 ... N ) \ { K } ) ) )

  proof
    wph
    cM
    cK
    cN
    cfz
    co
    wcel
    #
    cM
    c1
    caddc
    co
    #
    c1
    cN
    cfz
    co
    #
    cK
    csn
    #
    cdif
    wcel
    wph
    @0
    cK
    cM
    cle
    wbr
    #
    cM
    cN
    cle
    wbr
    #
    wa
    #
    wph
    @4
    @5
    submateqlem1.1
    wph
    cM
    cN
    c1
    cmin
    co
    #
    cN
    wph
    cM
    wph
    c1
    @7
    cfz
    co
    #
    cn
    cM
    @7
    fz1ssnn
    submateqlem1.m
    sseldi
    #
    nnred
    #
    wph
    cN
    c1
    wph
    cN
    submateqlem1.n
    nnred
    #
    wph
    1red
    resubcld
    @11
    wph
    cM
    @8
    wcel
    cM
    @7
    cle
    wbr
    #
    submateqlem1.m
    cM
    c1
    @7
    elfzle2
    syl
    #
    wph
    cN
    @11
    lem1d
    letrd
    jca
    wph
    cM
    cz
    wcel
    cK
    cz
    wcel
    cN
    cz
    wcel
    #
    @0
    @6
    wb
    wph
    cM
    @9
    nnzd
    #
    wph
    cK
    wph
    @2
    cn
    cK
    cN
    fz1ssnn
    submateqlem1.k
    sseldi
    #
    nnzd
    wph
    cN
    submateqlem1.n
    nnzd
    #
    cM
    cK
    cN
    elfz
    syl3anc
    mpbird
    wph
    @1
    @2
    @3
    wph
    @1
    @2
    wcel
    #
    c1
    @1
    cle
    wbr
    #
    @1
    cN
    cle
    wbr
    #
    wa
    #
    wph
    @19
    @20
    wph
    cc0
    cM
    cle
    wbr
    #
    @19
    wph
    cM
    wph
    cM
    @9
    nnnn0d
    #
    nn0ge0d
    wph
    c1
    cr
    wcel
    cM
    cr
    wcel
    @22
    @19
    wb
    1re
    @10
    c1
    cM
    addge02
    sylancr
    mpbid
    wph
    cM
    cN
    clt
    wbr
    #
    @20
    wph
    @24
    @12
    @13
    wph
    cM
    cn0
    wcel
    cN
    cn0
    wcel
    @24
    @12
    wb
    @23
    wph
    cN
    submateqlem1.n
    nnnn0d
    cM
    cN
    nn0ltlem1
    syl2anc
    mpbird
    wph
    cM
    cn
    wcel
    #
    cN
    cn
    wcel
    @24
    @20
    wb
    @9
    submateqlem1.n
    cM
    cN
    nnltp1le
    syl2anc
    mpbid
    jca
    wph
    @1
    cz
    wcel
    c1
    cz
    wcel
    @14
    @18
    @21
    wb
    wph
    cM
    @15
    peano2zd
    wph
    1zzd
    @17
    @1
    c1
    cN
    elfz
    syl3anc
    mpbird
    wph
    @1
    cK
    wne
    @1
    @3
    wcel
    wn
    wph
    cK
    @1
    wph
    cK
    @1
    wph
    cK
    @16
    nnred
    wph
    @4
    cK
    @1
    clt
    wbr
    #
    submateqlem1.1
    wph
    cK
    cn
    wcel
    @25
    @4
    @26
    wb
    @16
    @9
    cK
    cM
    nnleltp1
    syl2anc
    mpbid
    ltned
    necomd
    @1
    cK
    nelsn
    syl
    eldifd
    jca
end
