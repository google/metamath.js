include "c1.mm"
include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "cfz.mm"
include "csn.mm"
include "cdif.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wa.mm"
include "cmin.mm"
include "cn.mm"
include "fz1ssnn.mm"
include "sseldi.mm"
include "nnge1d.mm"
include "jca.mm"
include "cz.mm"
include "wb.mm"
include "nnzd.mm"
include "1zzd.mm"
include "elfzo.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "wceq.mm"
include "wo.mm"
include "orcd.mm"
include "cuz.mm"
include "cfv.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "fzm1.mm"
include "syl.mm"
include "wne.mm"
include "wn.mm"
include "nnred.mm"
include "ltned.mm"
include "nelsn.mm"
include "eldifd.mm"

theorem submateqlem2
  let wph: wff ph
  let cK: class K
  let cM: class M
  let cN: class N
  assume submateqlem2.n: |- ( ph -> N e. NN )
  assume submateqlem2.k: |- ( ph -> K e. ( 1 ... N ) )
  assume submateqlem2.m: |- ( ph -> M e. ( 1 ... ( N - 1 ) ) )
  assume submateqlem2.1: |- ( ph -> M < K )


  assert |- ( ph -> ( M e. ( 1 ..^ K ) /\ M e. ( ( 1 ... N ) \ { K } ) ) )

  proof
    wph
    cM
    c1
    cK
    cfzo
    co
    wcel
    #
    cM
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
    c1
    cM
    cle
    wbr
    #
    cM
    cK
    clt
    wbr
    #
    wa
    #
    wph
    @3
    @4
    wph
    cM
    wph
    c1
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    cn
    cM
    @6
    fz1ssnn
    submateqlem2.m
    sseldi
    #
    nnge1d
    submateqlem2.1
    jca
    wph
    cM
    cz
    wcel
    c1
    cz
    wcel
    cK
    cz
    wcel
    @0
    @5
    wb
    wph
    cM
    @8
    nnzd
    wph
    1zzd
    wph
    cK
    wph
    @1
    cn
    cK
    cN
    fz1ssnn
    submateqlem2.k
    sseldi
    nnzd
    cM
    c1
    cK
    elfzo
    syl3anc
    mpbird
    wph
    cM
    @1
    @2
    wph
    cM
    @1
    wcel
    #
    cM
    @7
    wcel
    #
    cM
    cN
    wceq
    #
    wo
    #
    wph
    @10
    @11
    submateqlem2.m
    orcd
    wph
    cN
    c1
    cuz
    cfv
    #
    wcel
    @9
    @12
    wb
    wph
    cN
    cn
    @13
    submateqlem2.n
    nnuz
    syl6eleq
    cM
    c1
    cN
    fzm1
    syl
    mpbird
    wph
    cM
    cK
    wne
    cM
    @2
    wcel
    wn
    wph
    cM
    cK
    wph
    cM
    @8
    nnred
    submateqlem2.1
    ltned
    cM
    cK
    nelsn
    syl
    eldifd
    jca
end
