include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cdiv.mm"
include "cbcc.mm"
include "cc.mm"
include "csn.mm"
include "eldifad.mm"
include "nncnd.mm"
include "1cnd.mm"
include "subcld.mm"
include "nnne0d.mm"
include "divcld.mm"
include "cn.mm"
include "wcel.mm"
include "cn0.mm"
include "nnm1nn0.mm"
include "syl.mm"
include "bcccl.mm"
include "cdif.mm"
include "wne.mm"
include "eldifsni.mm"
include "subne0d.mm"
include "divne0d.mm"
include "cmul.mm"
include "caddc.mm"
include "bccp1k.mm"
include "npcand.mm"
include "oveq2d.mm"
include "3eqtr3d.mm"
include "mulcomd.mm"
include "eqtr2d.mm"
include "mvllmuld.mm"

theorem bccm1k
  let wph: wff ph
  let cC: class C
  let cK: class K
  assume bccm1k.c: |- ( ph -> C e. ( CC \ { ( K - 1 ) } ) )
  assume bccm1k.k: |- ( ph -> K e. NN )


  assert |- ( ph -> ( C _Cc ( K - 1 ) ) = ( ( C _Cc K ) / ( ( C - ( K - 1 ) ) / K ) ) )

  proof
    wph
    cC
    cK
    c1
    cmin
    co
    #
    cmin
    co
    #
    cK
    cdiv
    co
    #
    cC
    @0
    cbcc
    co
    #
    cC
    cK
    cbcc
    co
    #
    wph
    @1
    cK
    wph
    cC
    @0
    wph
    cC
    cc
    @0
    csn
    #
    bccm1k.c
    eldifad
    #
    wph
    cK
    c1
    wph
    cK
    bccm1k.k
    nncnd
    #
    wph
    1cnd
    #
    subcld
    #
    subcld
    #
    @7
    wph
    cK
    bccm1k.k
    nnne0d
    #
    divcld
    #
    wph
    cC
    @0
    @6
    wph
    cK
    cn
    wcel
    @0
    cn0
    wcel
    bccm1k.k
    cK
    nnm1nn0
    syl
    #
    bcccl
    #
    wph
    @1
    cK
    @10
    @7
    wph
    cC
    @0
    @6
    @9
    wph
    cC
    cc
    @5
    cdif
    wcel
    cC
    @0
    wne
    bccm1k.c
    cC
    cc
    @0
    eldifsni
    syl
    subne0d
    @11
    divne0d
    wph
    @4
    @3
    @2
    cmul
    co
    #
    @2
    @3
    cmul
    co
    wph
    cC
    @0
    c1
    caddc
    co
    #
    cbcc
    co
    @3
    @1
    @16
    cdiv
    co
    #
    cmul
    co
    @4
    @15
    wph
    cC
    @0
    @6
    @13
    bccp1k
    wph
    @16
    cK
    cC
    cbcc
    wph
    cK
    c1
    @7
    @8
    npcand
    #
    oveq2d
    wph
    @17
    @2
    @3
    cmul
    wph
    @16
    cK
    @1
    cdiv
    @18
    oveq2d
    oveq2d
    3eqtr3d
    wph
    @3
    @2
    @14
    @12
    mulcomd
    eqtr2d
    mvllmuld
end
