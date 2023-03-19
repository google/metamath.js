include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cppi.mm"
include "cmin.mm"
include "co.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "cfz.mm"
include "cprime.mm"
include "cin.mm"
include "chash.mm"
include "c1.mm"
include "caddc.mm"
include "cun.mm"
include "cz.mm"
include "wceq.mm"
include "eluzelz.mm"
include "eluzel2.mm"
include "2z.mm"
include "ifcl.mm"
include "sylancl.mm"
include "a1i.mm"
include "cr.mm"
include "zred.mm"
include "2re.mm"
include "min2.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "ppival2g.mm"
include "syl2anc.mm"
include "min1.mm"
include "id.mm"
include "elfzuzb.mm"
include "sylanbrc.mm"
include "fzsplit.mm"
include "syl.mm"
include "ineq1d.mm"
include "indir.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "c0.mm"
include "clt.mm"
include "ltp1d.mm"
include "fzdisj.mm"
include "inindir.mm"
include "0in.mm"
include "3eqtr3g.mm"
include "cfn.mm"
include "wss.mm"
include "fzfi.mm"
include "inss1.mm"
include "ssfi.mm"
include "mp2an.mm"
include "hashun.mm"
include "mp3an12.mm"
include "3eqtrd.mm"
include "oveq12d.mm"
include "cc.mm"
include "cn0.mm"
include "hashcl.mm"
include "ax-mp.mm"
include "nn0cni.mm"
include "pncan2.mm"

theorem ppidif
  let cM: class M
  let cN: class N


  assert |- ( N e. ( ZZ>= ` M ) -> ( ( ppi ` N ) - ( ppi ` M ) ) = ( # ` ( ( ( M + 1 ) ... N ) i^i Prime ) ) )

  proof
    cN
    cM
    cuz
    cfv
    wcel
    #
    cN
    cppi
    cfv
    #
    cM
    cppi
    cfv
    #
    cmin
    co
    cM
    c2
    cle
    wbr
    #
    cM
    c2
    cif
    #
    cM
    cfz
    co
    #
    cprime
    cin
    #
    chash
    cfv
    #
    cM
    c1
    caddc
    co
    #
    cN
    cfz
    co
    #
    cprime
    cin
    #
    chash
    cfv
    #
    caddc
    co
    #
    @7
    cmin
    co
    #
    @11
    @0
    @1
    @12
    @2
    @7
    cmin
    @0
    @1
    @4
    cN
    cfz
    co
    #
    cprime
    cin
    #
    chash
    cfv
    #
    @6
    @10
    cun
    #
    chash
    cfv
    #
    @12
    @0
    cN
    cz
    wcel
    c2
    @4
    cuz
    cfv
    #
    wcel
    #
    @1
    @16
    wceq
    cM
    cN
    eluzelz
    @0
    @4
    cz
    wcel
    #
    c2
    cz
    wcel
    #
    @4
    c2
    cle
    wbr
    #
    @20
    @0
    cM
    cz
    wcel
    #
    @22
    @21
    cM
    cN
    eluzel2
    #
    2z
    @3
    cM
    c2
    cz
    ifcl
    sylancl
    #
    @22
    @0
    2z
    a1i
    @0
    cM
    cr
    wcel
    #
    c2
    cr
    wcel
    #
    @23
    @0
    cM
    @25
    zred
    #
    2re
    cM
    c2
    min2
    sylancl
    @4
    c2
    eluz2
    syl3anbrc
    #
    cN
    @4
    ppival2g
    syl2anc
    @0
    @15
    @17
    chash
    @0
    @15
    @5
    @9
    cun
    #
    cprime
    cin
    @17
    @0
    @14
    @31
    cprime
    @0
    cM
    @14
    wcel
    #
    @14
    @31
    wceq
    @0
    cM
    @19
    wcel
    #
    @0
    @32
    @0
    @21
    @24
    @4
    cM
    cle
    wbr
    #
    @33
    @26
    @25
    @0
    @27
    @28
    @34
    @29
    2re
    cM
    c2
    min1
    sylancl
    @4
    cM
    eluz2
    syl3anbrc
    @0
    id
    cM
    @4
    cN
    elfzuzb
    sylanbrc
    cM
    @4
    cN
    fzsplit
    syl
    ineq1d
    @5
    @9
    cprime
    indir
    syl6eq
    fveq2d
    @0
    @6
    @10
    cin
    #
    c0
    wceq
    #
    @18
    @12
    wceq
    #
    @0
    @5
    @9
    cin
    #
    cprime
    cin
    c0
    cprime
    cin
    @35
    c0
    @0
    @38
    c0
    cprime
    @0
    cM
    @8
    clt
    wbr
    @38
    c0
    wceq
    @0
    cM
    @29
    ltp1d
    @4
    cM
    @8
    cN
    fzdisj
    syl
    ineq1d
    @5
    @9
    cprime
    inindir
    cprime
    0in
    3eqtr3g
    @6
    cfn
    wcel
    #
    @10
    cfn
    wcel
    #
    @36
    @37
    @5
    cfn
    wcel
    @6
    @5
    wss
    @39
    @4
    cM
    fzfi
    @5
    cprime
    inss1
    @5
    @6
    ssfi
    mp2an
    #
    @9
    cfn
    wcel
    @10
    @9
    wss
    @40
    @8
    cN
    fzfi
    @9
    cprime
    inss1
    @9
    @10
    ssfi
    mp2an
    #
    @6
    @10
    hashun
    mp3an12
    syl
    3eqtrd
    @0
    @24
    @20
    @2
    @7
    wceq
    @25
    @30
    cM
    @4
    ppival2g
    syl2anc
    oveq12d
    @7
    cc
    wcel
    @11
    cc
    wcel
    @13
    @11
    wceq
    @7
    @39
    @7
    cn0
    wcel
    @41
    @6
    hashcl
    ax-mp
    nn0cni
    @11
    @40
    @11
    cn0
    wcel
    @42
    @10
    hashcl
    ax-mp
    nn0cni
    @7
    @11
    pncan2
    mp2an
    syl6eq
end
