include "cc0.mm"
include "c1.mm"
include "c3.mm"
include "ctp.mm"
include "c2.mm"
include "cv.mm"
include "cvtxdg.mm"
include "cfv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "crab.mm"
include "wss.mm"
include "chash.mm"
include "cle.mm"
include "clt.mm"
include "konigsberglem4.mm"
include "cvv.mm"
include "wcel.mm"
include "cfz.mm"
include "ovexi.mm"
include "rabex.mm"
include "hashss.mm"
include "mpan.mm"
include "wne.mm"
include "w3a.mm"
include "wceq.mm"
include "0ne1.mm"
include "1re.mm"
include "1lt3.mm"
include "ltneii.mm"
include "3ne0.mm"
include "3pm3.2i.mm"
include "wb.mm"
include "c0ex.mm"
include "1ex.mm"
include "3ex.mm"
include "hashtpg.mm"
include "mp3an.mm"
include "mpbi.mm"
include "breq1i.mm"
include "caddc.mm"
include "co.mm"
include "df-3.mm"
include "cz.mm"
include "2z.mm"
include "cfn.mm"
include "cn0.mm"
include "fzfi.mm"
include "eqeltri.mm"
include "rabfi.mm"
include "hashcl.mm"
include "mp2b.mm"
include "nn0zi.mm"
include "zltp1le.mm"
include "mp2an.mm"
include "sylbb2.mm"
include "sylbi.mm"

theorem konigsberglem5
  let vx: setvar x
  let cE: class E
  let cG: class G
  let cV: class V
  assume konigsberg.v: |- V = ( 0 ... 3 )
  assume konigsberg.e: |- E = <" { 0 , 1 } { 0 , 2 } { 0 , 3 } { 1 , 2 } { 1 , 2 } { 2 , 3 } { 2 , 3 } ">
  assume konigsberg.g: |- G = <. V , E >.

  disjoint V x
  disjoint G x
  assert |- 2 < ( # ` { x e. V | -. 2 || ( ( VtxDeg ` G ) ` x ) } )

  proof
    cc0
    c1
    c3
    ctp
    #
    c2
    vx
    cv
    cG
    cvtxdg
    cfv
    cfv
    cdvds
    wbr
    wn
    #
    vx
    cV
    crab
    #
    wss
    #
    @0
    chash
    cfv
    #
    @2
    chash
    cfv
    #
    cle
    wbr
    #
    c2
    @5
    clt
    wbr
    #
    vx
    cE
    cG
    cV
    konigsberg.v
    konigsberg.e
    konigsberg.g
    konigsberglem4
    @2
    cvv
    wcel
    @3
    @6
    @1
    vx
    cV
    cV
    cc0
    c3
    cfz
    konigsberg.v
    ovexi
    rabex
    @2
    @0
    cvv
    hashss
    mpan
    @6
    c3
    @5
    cle
    wbr
    #
    @7
    @4
    c3
    @5
    cle
    cc0
    c1
    wne
    #
    c1
    c3
    wne
    #
    c3
    cc0
    wne
    #
    w3a
    #
    @4
    c3
    wceq
    #
    @9
    @10
    @11
    0ne1
    c1
    c3
    1re
    1lt3
    ltneii
    3ne0
    3pm3.2i
    cc0
    cvv
    wcel
    c1
    cvv
    wcel
    c3
    cvv
    wcel
    @12
    @13
    wb
    c0ex
    1ex
    3ex
    cc0
    c1
    c3
    cvv
    cvv
    cvv
    hashtpg
    mp3an
    mpbi
    breq1i
    @8
    c2
    c1
    caddc
    co
    #
    @5
    cle
    wbr
    #
    @7
    c3
    @14
    @5
    cle
    df-3
    breq1i
    c2
    cz
    wcel
    @5
    cz
    wcel
    @7
    @15
    wb
    2z
    @5
    cV
    cfn
    wcel
    @2
    cfn
    wcel
    @5
    cn0
    wcel
    cV
    cc0
    c3
    cfz
    co
    cfn
    konigsberg.v
    cc0
    c3
    fzfi
    eqeltri
    @1
    vx
    cV
    rabfi
    @2
    hashcl
    mp2b
    nn0zi
    c2
    @5
    zltp1le
    mp2an
    sylbb2
    sylbi
    mp2b
end
